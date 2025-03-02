//! Compute the binary representation of a type

use adt::layout_of_adt_query;
use base_db::ra_salsa::Cycle;
use hir_def::{
    layout::{
        BackendRepr, FieldsShape, Float, Integer, LayoutCalculator, LayoutCalculatorError,
        Primitive, ReprOptions, Scalar, Size, StructKind, TargetDataLayout, WrappingRange,
    },
    AdtId, LocalFieldId, OpaqueTyLoc, StructId,
};
use la_arena::Idx;
use rustc_abi::AddressSpace;
use rustc_hashes::Hash64;
use rustc_index::{IndexSlice, IndexVec};

use rustc_type_ir::{
    inherent::{IntoKind, SliceLike},
    FloatTy, IntTy, TyKind, UintTy,
};
use triomphe::Arc;

use crate::{
    consteval_nextsolver::try_const_usize,
    db::HirDatabase,
    layout::{
        adt::struct_variant_idx, Layout, LayoutError, RustcEnumVariantIdx, RustcFieldIdx, Variants,
    },
    lower_nextsolver::field_types_query,
    next_solver::{DbInterner, GenericArgs, Ty},
    TraitEnvironment,
};

mod adt;

struct LayoutCx<'a> {
    calc: LayoutCalculator<&'a TargetDataLayout>,
}

impl<'a> LayoutCx<'a> {
    fn new(target: &'a TargetDataLayout) -> Self {
        Self { calc: LayoutCalculator::new(target) }
    }
}

// FIXME: move this to the `rustc_abi`.
fn layout_of_simd_ty(
    db: &dyn HirDatabase,
    id: StructId,
    args: &GenericArgs,
    env: Arc<TraitEnvironment>,
    dl: &TargetDataLayout,
) -> Result<Arc<Layout>, LayoutError> {
    let fields = field_types_query(db, id.into());

    // Supported SIMD vectors are homogeneous ADTs with at least one field:
    //
    // * #[repr(simd)] struct S(T, T, T, T);
    // * #[repr(simd)] struct S { it: T, y: T, z: T, w: T }
    // * #[repr(simd)] struct S([T; 4])
    //
    // where T is a primitive scalar (integer/float/pointer).

    let f0_ty = match fields.iter().next() {
        Some(it) => it.1.clone().instantiate(DbInterner, args),
        None => return Err(LayoutError::InvalidSimdType),
    };

    // The element type and number of elements of the SIMD vector
    // are obtained from:
    //
    // * the element type and length of the single array field, if
    // the first field is of array type, or
    //
    // * the homogeneous field type and the number of fields.
    let (e_ty, e_len, is_array) = if let TyKind::Array(e_ty, _) = f0_ty.clone().kind() {
        // Extract the number of elements from the layout of the array field:
        let FieldsShape::Array { count, .. } =
            layout_of_ty_query(db, f0_ty.clone(), env.clone())?.fields
        else {
            return Err(LayoutError::Unknown);
        };

        (e_ty.clone(), count, true)
    } else {
        // First ADT field is not an array:
        (f0_ty, fields.iter().count() as u64, false)
    };

    // Compute the ABI of the element type:
    let e_ly = layout_of_ty_query(db, e_ty, env)?;
    let BackendRepr::Scalar(e_abi) = e_ly.backend_repr else {
        return Err(LayoutError::Unknown);
    };

    // Compute the size and alignment of the vector:
    let size = e_ly
        .size
        .checked_mul(e_len, dl)
        .ok_or(LayoutError::BadCalc(LayoutCalculatorError::SizeOverflow))?;
    let align = dl.llvmlike_vector_align(size);
    let size = size.align_to(align.abi);

    // Compute the placement of the vector fields:
    let fields = if is_array {
        FieldsShape::Arbitrary { offsets: [Size::ZERO].into(), memory_index: [0].into() }
    } else {
        FieldsShape::Array { stride: e_ly.size, count: e_len }
    };

    Ok(Arc::new(Layout {
        variants: Variants::Single { index: struct_variant_idx() },
        fields,
        backend_repr: BackendRepr::Vector { element: e_abi, count: e_len },
        largest_niche: e_ly.largest_niche,
        size,
        align,
        max_repr_align: None,
        unadjusted_abi_align: align.abi,
        uninhabited: false,
        randomization_seed: Hash64::ZERO,
    }))
}

pub fn layout_of_ty_query(
    db: &dyn HirDatabase,
    ty: Ty,
    trait_env: Arc<TraitEnvironment>,
) -> Result<Arc<Layout>, LayoutError> {
    let krate = trait_env.krate;
    let Ok(target) = db.target_data_layout(krate) else {
        return Err(LayoutError::TargetLayoutNotAvailable);
    };
    let dl = &*target;
    let cx = LayoutCx::new(dl);
    //let ty = normalize(db, trait_env.clone(), ty);
    let result = match ty.clone().kind() {
        TyKind::Adt(def, args) => {
            match def.0.id {
                hir_def::AdtId::StructId(s) => {
                    let data = db.struct_data(s);
                    let repr = data.repr.unwrap_or_default();
                    if repr.simd() {
                        return layout_of_simd_ty(db, s, &args, trait_env, &target);
                    }
                }
                _ => {}
            }
            return layout_of_adt_query(db, def.0.id, &args, trait_env);
        }
        TyKind::Bool => Layout::scalar(
            dl,
            Scalar::Initialized {
                value: Primitive::Int(Integer::I8, false),
                valid_range: WrappingRange { start: 0, end: 1 },
            },
        ),
        TyKind::Char => Layout::scalar(
            dl,
            Scalar::Initialized {
                value: Primitive::Int(Integer::I32, false),
                valid_range: WrappingRange { start: 0, end: 0x10FFFF },
            },
        ),
        TyKind::Int(i) => scalar(
            dl,
            Primitive::Int(
                match i {
                    IntTy::Isize => dl.ptr_sized_integer(),
                    IntTy::I8 => Integer::I8,
                    IntTy::I16 => Integer::I16,
                    IntTy::I32 => Integer::I32,
                    IntTy::I64 => Integer::I64,
                    IntTy::I128 => Integer::I128,
                },
                true,
            ),
        ),
        TyKind::Uint(i) => scalar(
            dl,
            Primitive::Int(
                match i {
                    UintTy::Usize => dl.ptr_sized_integer(),
                    UintTy::U8 => Integer::I8,
                    UintTy::U16 => Integer::I16,
                    UintTy::U32 => Integer::I32,
                    UintTy::U64 => Integer::I64,
                    UintTy::U128 => Integer::I128,
                },
                false,
            ),
        ),
        TyKind::Float(f) => scalar(
            dl,
            Primitive::Float(match f {
                FloatTy::F16 => Float::F16,
                FloatTy::F32 => Float::F32,
                FloatTy::F64 => Float::F64,
                FloatTy::F128 => Float::F128,
            }),
        ),
        TyKind::Tuple(tys) => {
            let kind =
                if tys.len() == 0 { StructKind::AlwaysSized } else { StructKind::MaybeUnsized };

            let fields = tys
                .iter()
                .map(|k| layout_of_ty_query(db, k, trait_env.clone()))
                .collect::<Result<Vec<_>, _>>()?;
            let fields = fields.iter().map(|it| &**it).collect::<Vec<_>>();
            let fields = fields.iter().collect::<IndexVec<_, _>>();
            cx.calc.univariant(&fields, &ReprOptions::default(), kind)?
        }
        TyKind::Array(element, count) => {
            let count = try_const_usize(db, &count).ok_or(LayoutError::HasErrorConst)? as u64;
            let element = layout_of_ty_query(db, element.clone(), trait_env)?;
            let size = element
                .size
                .checked_mul(count, dl)
                .ok_or(LayoutError::BadCalc(LayoutCalculatorError::SizeOverflow))?;

            let backend_repr = BackendRepr::Memory { sized: true };
            let largest_niche = if count != 0 { element.largest_niche } else { None };
            let uninhabited = element.uninhabited || count == 0;

            Layout {
                variants: Variants::Single { index: struct_variant_idx() },
                fields: FieldsShape::Array { stride: element.size, count },
                backend_repr,
                largest_niche,
                align: element.align,
                size,
                max_repr_align: None,
                unadjusted_abi_align: element.align.abi,
                uninhabited,
                randomization_seed: Hash64::ZERO,
            }
        }
        TyKind::Slice(element) => {
            let element = layout_of_ty_query(db, element.clone(), trait_env)?;
            Layout {
                variants: Variants::Single { index: struct_variant_idx() },
                fields: FieldsShape::Array { stride: element.size, count: 0 },
                backend_repr: BackendRepr::Memory { sized: false },
                largest_niche: None,
                align: element.align,
                size: Size::ZERO,
                max_repr_align: None,
                unadjusted_abi_align: element.align.abi,
                uninhabited: element.uninhabited,
                randomization_seed: Hash64::ZERO,
            }
        }
        TyKind::Str => Layout {
            variants: Variants::Single { index: struct_variant_idx() },
            fields: FieldsShape::Array { stride: Size::from_bytes(1), count: 0 },
            backend_repr: BackendRepr::Memory { sized: false },
            largest_niche: None,
            align: dl.i8_align,
            size: Size::ZERO,
            max_repr_align: None,
            unadjusted_abi_align: dl.i8_align.abi,
            uninhabited: false,
            randomization_seed: Hash64::ZERO,
        },
        // Potentially-wide pointers.
        TyKind::Ref(_, pointee, _) | TyKind::RawPtr(pointee, _) => {
            let mut data_ptr = scalar_unit(dl, Primitive::Pointer(AddressSpace::DATA));
            if matches!(ty.clone().kind(), TyKind::Ref(..)) {
                data_ptr.valid_range_mut().start = 1;
            }

            // let pointee = tcx.normalize_erasing_regions(param_env, pointee);
            // if pointee.is_sized(tcx.at(DUMMY_SP), param_env) {
            //     return Ok(tcx.mk_layout(LayoutS::scalar(cx, data_ptr)));
            // }

            let unsized_part = struct_tail_erasing_lifetimes(db, pointee.clone());
            /*
            if let TyKind::AssociatedType(id, subst) = unsized_part.kind(Interner) {
                unsized_part = TyKind::Alias(chalk_ir::AliasTy::Projection(ProjectionTy {
                    associated_ty_id: *id,
                    substitution: subst.clone(),
                }))
                .intern(Interner);
            }
            unsized_part = normalize(db, trait_env, unsized_part);
            */
            let metadata = match unsized_part.kind() {
                TyKind::Slice(_) | TyKind::Str => {
                    scalar_unit(dl, Primitive::Int(dl.ptr_sized_integer(), false))
                }
                TyKind::Dynamic(..) => {
                    let mut vtable = scalar_unit(dl, Primitive::Pointer(AddressSpace::DATA));
                    vtable.valid_range_mut().start = 1;
                    vtable
                }
                _ => {
                    // pointee is sized
                    return Ok(Arc::new(Layout::scalar(dl, data_ptr)));
                }
            };

            // Effectively a (ptr, meta) tuple.
            cx.calc.scalar_pair(data_ptr, metadata)
        }
        TyKind::FnDef(_, _) => layout_of_unit(&cx)?,
        TyKind::Never => cx.calc.layout_of_never_type(),
        TyKind::Dynamic(..) | TyKind::Foreign(_) => {
            let mut unit = layout_of_unit(&cx)?;
            match &mut unit.backend_repr {
                BackendRepr::Memory { sized } => *sized = false,
                _ => return Err(LayoutError::Unknown),
            }
            unit
        }
        TyKind::FnPtr(..) => {
            let mut ptr = scalar_unit(dl, Primitive::Pointer(dl.instruction_address_space));
            ptr.valid_range_mut().start = 1;
            Layout::scalar(dl, ptr)
        }
        TyKind::Alias(_, ty) => match ty.def_id {
            hir_def::GenericDefId::TypeAliasId(_) => todo!(),
            hir_def::GenericDefId::OpaqueTyId(opaque) => {
                let impl_trait_id = db.lookup_intern_opaque_ty(opaque);
                match impl_trait_id {
                    OpaqueTyLoc::ReturnTypeImplTrait(func, idx) => {
                        let infer = db.infer(func.into());
                        return db.layout_of_ty(
                            infer.type_of_rpit[Idx::from_raw(idx)].clone(),
                            trait_env,
                        );
                    }
                    OpaqueTyLoc::TypeAliasImplTrait(..) => {
                        return Err(LayoutError::NotImplemented);
                    }
                    OpaqueTyLoc::AsyncBlockTypeImplTrait(_, _) => {
                        return Err(LayoutError::NotImplemented)
                    }
                }
            }
            _ => unreachable!(),
        },
        TyKind::Closure(_, _) => {
            todo!()
            /*
            let fake_ir = crate::next_solver::DbIr::new(db, CrateId::from_raw(la_arena::RawIdx::from_u32(0)), None);
            let def = match c {
                hir_def::GenericDefId::ClosureId(id) => id,
                _ => unreachable!(),
            };
            let def = db.lookup_intern_closure_def(def);
            let infer = db.infer(def.parent);
            let (captures, _) = infer.closure_info(&def);
            let fields = captures
                .iter()
                .map(|it| {
                    layout_of_ty_query(
                        it.ty.clone().substitute(Interner, ClosureSubst(subst).parent_subst()),
                        trait_env.clone(),
                    )
                })
                .collect::<Result<Vec<_>, _>>()?;
            let fields = fields.iter().map(|it| &**it).collect::<Vec<_>>();
            let fields = fields.iter().collect::<IndexVec<_, _>>();
            cx.calc.univariant(&fields, &ReprOptions::default(), StructKind::AlwaysSized)?
            */
        }
        TyKind::Coroutine(_, _) | TyKind::CoroutineWitness(_, _) => {
            return Err(LayoutError::NotImplemented)
        }
        TyKind::Error(_) => return Err(LayoutError::HasErrorType),
        TyKind::Placeholder(_) | TyKind::Bound(..) | TyKind::Infer(..) | TyKind::Param(..) => {
            return Err(LayoutError::HasPlaceholder)
        }
        TyKind::Pat(..) | TyKind::CoroutineClosure(..) => todo!(),
    };
    Ok(Arc::new(result))
}

pub fn layout_of_ty_recover(
    _: &dyn HirDatabase,
    _: &Cycle,
    _: &Ty,
    _: &Arc<TraitEnvironment>,
) -> Result<Arc<Layout>, LayoutError> {
    Err(LayoutError::RecursiveTypeWithoutIndirection)
}

fn layout_of_unit(cx: &LayoutCx<'_>) -> Result<Layout, LayoutError> {
    cx.calc
        .univariant::<RustcFieldIdx, RustcEnumVariantIdx, &&Layout>(
            IndexSlice::empty(),
            &ReprOptions::default(),
            StructKind::AlwaysSized,
        )
        .map_err(Into::into)
}

fn struct_tail_erasing_lifetimes(db: &dyn HirDatabase, pointee: Ty) -> Ty {
    match pointee.clone().kind() {
        TyKind::Adt(def, args) => {
            let struct_id = match def.0.id {
                AdtId::StructId(id) => id,
                _ => return pointee,
            };
            let data = db.struct_data(struct_id);
            let mut it = data.variant_data.fields().iter().rev();
            match it.next() {
                Some((f, _)) => {
                    let last_field_ty = field_ty(db, struct_id.into(), f, &args);
                    struct_tail_erasing_lifetimes(db, last_field_ty)
                }
                None => pointee,
            }
        }
        _ => pointee,
    }
}

fn field_ty(
    db: &dyn HirDatabase,
    def: hir_def::VariantId,
    fd: LocalFieldId,
    args: &GenericArgs,
) -> Ty {
    field_types_query(db, def)[fd].clone().instantiate(DbInterner, args)
}

fn scalar_unit(dl: &TargetDataLayout, value: Primitive) -> Scalar {
    Scalar::Initialized { value, valid_range: WrappingRange::full(value.size(dl)) }
}

fn scalar(dl: &TargetDataLayout, value: Primitive) -> Layout {
    Layout::scalar(dl, scalar_unit(dl, value))
}
