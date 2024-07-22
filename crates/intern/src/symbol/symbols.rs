//! Module defining all known symbols required by the rest of rust-analyzer.
#![allow(non_upper_case_globals)]

use std::hash::{BuildHasherDefault, Hash as _, Hasher as _};

use dashmap::{DashMap, SharedValue};
use rustc_hash::FxHasher;

use crate::{
    symbol::{SymbolProxy, TaggedArcPtr},
    Symbol,
};

macro_rules! define_symbols {
    (@WITH_NAME: $($alias:ident = $value:literal,)* @PLAIN: $($name:ident,)*) => {
        // Ideally we would be emitting `const` here, but then we no longer have stable addresses
        // which is what we are relying on for equality! In the future if consts can refer to
        // statics we should swap these for `const`s and have the the string literal being pointed
        // to be statics to refer to such that their address is stable.
        $(
            pub static $name: Symbol = Symbol { repr: TaggedArcPtr::non_arc(&stringify!($name)) };
        )*
        $(
            pub static $alias: Symbol = Symbol { repr: TaggedArcPtr::non_arc(&$value) };
        )*


        pub(super) fn prefill() -> DashMap<SymbolProxy, (), BuildHasherDefault<FxHasher>> {
            let mut dashmap_ = <DashMap<SymbolProxy, (), BuildHasherDefault<FxHasher>>>::with_hasher(BuildHasherDefault::default());

            let hash_thing_ = |hasher_: &BuildHasherDefault<FxHasher>, it_: &SymbolProxy| {
                let mut hasher_ = std::hash::BuildHasher::build_hasher(hasher_);
                it_.hash(&mut hasher_);
                hasher_.finish()
            };
            {
                $(

                    let proxy_ = SymbolProxy($name.repr);
                    let hash_ = hash_thing_(dashmap_.hasher(), &proxy_);
                    let shard_idx_ = dashmap_.determine_shard(hash_ as usize);
                    dashmap_.shards_mut()[shard_idx_].get_mut().raw_entry_mut().from_hash(hash_, |k| k == &proxy_).insert(proxy_, SharedValue::new(()));
                )*
                $(

                    let proxy_ = SymbolProxy($alias.repr);
                    let hash_ = hash_thing_(dashmap_.hasher(), &proxy_);
                    let shard_idx_ = dashmap_.determine_shard(hash_ as usize);
                    dashmap_.shards_mut()[shard_idx_].get_mut().raw_entry_mut().from_hash(hash_, |k| k == &proxy_).insert(proxy_, SharedValue::new(()));
                )*
            }
            dashmap_
        }
    };
}
define_symbols! {
    @WITH_NAME:

    INTEGER_0 = "0",
    INTEGER_1 = "1",
    INTEGER_2 = "2",
    INTEGER_3 = "3",
    INTEGER_4 = "4",
    INTEGER_5 = "5",
    INTEGER_6 = "6",
    INTEGER_7 = "7",
    INTEGER_8 = "8",
    INTEGER_9 = "9",
    INTEGER_10 = "10",
    INTEGER_11 = "11",
    INTEGER_12 = "12",
    INTEGER_13 = "13",
    INTEGER_14 = "14",
    INTEGER_15 = "15",
    __empty = "",
    unsafe_ = "unsafe",
    in_ = "in",
    super_ = "super",
    self_ = "self",
    Self_ = "Self",
    tick_static = "'static",
    dollar_crate = "$crate",
    MISSING_NAME = "[missing name]",
    fn_ = "fn",
    crate_ = "crate",
    underscore = "_",
    true_ = "true",
    false_ = "false",
    let_ = "let",
    const_ = "const",
    proc_dash_macro = "proc-macro",
    aapcs_dash_unwind = "aapcs-unwind",
    avr_dash_interrupt = "avr-interrupt",
    avr_dash_non_dash_blocking_dash_interrupt = "avr-non-blocking-interrupt",
    C_dash_cmse_dash_nonsecure_dash_call = "C-cmse-nonsecure-call",
    C_dash_unwind = "C-unwind",
    cdecl_dash_unwind = "cdecl-unwind",
    fastcall_dash_unwind = "fastcall-unwind",
    msp430_dash_interrupt = "msp430-interrupt",
    platform_dash_intrinsic = "platform-intrinsic",
    ptx_dash_kernel = "ptx-kernel",
    riscv_dash_interrupt_dash_m = "riscv-interrupt-m",
    riscv_dash_interrupt_dash_s = "riscv-interrupt-s",
    rust_dash_call = "rust-call",
    rust_dash_cold = "rust-cold",
    rust_dash_intrinsic = "rust-intrinsic",
    stdcall_dash_unwind = "stdcall-unwind",
    system_dash_unwind = "system-unwind",
    sysv64_dash_unwind = "sysv64-unwind",
    thiscall_dash_unwind = "thiscall-unwind",
    vectorcall_dash_unwind = "vectorcall-unwind",
    win64_dash_unwind = "win64-unwind",
    x86_dash_interrupt = "x86-interrupt",

    @PLAIN:
    __ra_fixup,
    aapcs,
    add_assign,
    add,
    alias,
    align_offset,
    align,
    all,
    alloc_layout,
    alloc,
    allow_internal_unsafe,
    allow,
    any,
    as_str,
    asm,
    assert,
    attributes,
    begin_panic,
    bench,
    bitand_assign,
    bitand,
    bitor_assign,
    bitor,
    bitxor_assign,
    bitxor,
    bool,
    box_free,
    Box,
    boxed,
    branch,
    Break,
    c_void,
    C,
    call_mut,
    call_once,
    call,
    cdecl,
    Center,
    cfg_accessible,
    cfg_attr,
    cfg_eval,
    cfg,
    char,
    clone,
    Clone,
    coerce_unsized,
    column,
    compile_error,
    concat_bytes,
    concat_idents,
    concat,
    const_format_args,
    const_panic_fmt,
    const_param_ty,
    Context,
    Continue,
    copy,
    Copy,
    core_panic,
    core,
    coroutine_state,
    coroutine,
    count,
    crate_type,
    CStr,
    debug_assertions,
    Debug,
    default,
    Default,
    deprecated,
    deref_mut,
    deref_target,
    deref,
    derive_const,
    derive,
    discriminant_kind,
    discriminant_type,
    dispatch_from_dyn,destruct,
    div_assign,
    div,
    doc,
    drop_in_place,
    drop,
    dyn_metadata,
    efiapi,
    eh_catch_typeinfo,
    eh_personality,
    env,
    eq,
    Eq,
    Err,
    exchange_malloc,
    exhaustive_patterns,
    export_name,
    f128,
    f16,
    f32,
    f64,
    fastcall,
    feature,
    file,
    filter_map,
    fmt,
    fn_mut,
    fn_once_output,
    fn_once,
    fn_ptr_addr,
    fn_ptr_trait,
    format_alignment,
    format_args_nl,
    format_args,
    format_argument,
    format_arguments,
    format_count,
    format_placeholder,
    format_unsafe_arg,
    format,
    freeze,
    from_output,
    from_residual,
    from_usize,
    from_yeet,
    fundamental,
    future_trait,
    future,
    Future,
    ge,
    get_context,
    global_allocator,
    global_asm,
    gt,
    Hash,
    hidden,
    html_root_url,
    i128,
    i16,
    i32,
    i64,
    i8,
    ignore,
    Implied,
    include_bytes,
    include_str,
    include,
    index_mut,
    index,
    Index,
    into_future,
    into_iter,
    IntoFuture,
    IntoIter,
    IntoIterator,
    is_empty,
    Is,
    isize,
    Item,
    iter_mut,
    iter,
    Iterator,
    keyword,
    lang,
    le,
    Left,
    len,
    line,
    llvm_asm,
    local_inner_macros,
    log_syntax,
    lt,
    macro_export,
    macro_rules,
    macro_use,
    main,
    manually_drop,
    may_dangle,
    maybe_uninit,
    metadata_type,
    min_exhaustive_patterns,
    miri,
    missing,
    module_path,
    mul_assign,
    mul,
    ne,
    neg,
    Neg,
    new_binary,
    new_debug,
    new_display,
    new_lower_exp,
    new_lower_hex,
    new_octal,
    new_pointer,
    new_unchecked,
    new_upper_exp,
    new_upper_hex,
    new_v1_formatted,
    new,
    next,
    no_core,
    no_mangle,
    no_std,
    non_exhaustive,
    none,
    None,
    not,
    Not,
    notable_trait,
    Ok,
    opaque,
    ops,
    option_env,
    option,
    Option,
    Ord,
    Output,
    owned_box,
    packed,
    panic_2015,
    panic_2021,
    panic_bounds_check,
    panic_cannot_unwind,
    panic_display,
    panic_fmt,
    panic_impl,
    panic_info,
    panic_location,
    panic_misaligned_pointer_dereference,
    panic_nounwind,
    panic,
    Param,
    partial_ord,
    PartialEq,
    PartialOrd,
    path,
    Pending,
    phantom_data,
    pieces,
    pin,
    pointee_trait,
    pointer_like,
    poll,
    Poll,
    prelude_import,
    prelude,
    proc_macro_attribute,
    proc_macro_derive,
    proc_macro,
    quote,
    range_inclusive_new,
    Range,
    RangeFrom,
    RangeFull,
    RangeInclusive,
    RangeTo,
    RangeToInclusive,
    Ready,
    receiver,
    recursion_limit,
    register_attr,
    register_tool,
    rem_assign,
    rem,
    repr,
    result,
    Result,
    ResumeTy,
    Right,
    rust_2015,
    rust_2018,
    rust_2021,
    rust_2024,
    rust_analyzer,
    Rust,
    rustc_allow_incoherent_impl,
    rustc_builtin_macro,
    rustc_coherence_is_core,
    rustc_const_panic_str,
    rustc_deprecated_safe_2024,
    rustc_has_incoherent_inherent_impls,
    rustc_layout_scalar_valid_range_end,
    rustc_layout_scalar_valid_range_start,
    rustc_legacy_const_generics,
    rustc_macro_transparency,
    rustc_reservation_impl,
    rustc_safe_intrinsic,
    rustc_skip_array_during_method_dispatch,
    rustc_skip_during_method_dispatch,
    semitransparent,
    shl_assign,
    shl,
    shr_assign,
    shr,
    simd,
    sized,
    slice_len_fn,
    Some,
    start,
    std_panic,
    std,
    stdcall,
    str,
    string,
    String,
    stringify,
    structural_peq,
    structural_teq,
    sub_assign,
    sub,
    sync,
    system,
    sysv64,
    Target,
    termination,
    test_case,
    test,
    thiscall,
    trace_macros,
    transmute_opts,
    transmute_trait,
    transparent,
    Try,
    tuple_trait,
    u128,
    u16,
    u32,
    u64,
    u8,
    unadjusted,
    Unknown,
    unpin,
    unreachable_2015,
    unreachable_2021,
    unreachable,
    unsafe_cell,
    unsize,
    unstable,
    usize,
    v1,
    va_list,
    vectorcall,
    wasm,
    win64,
    array,
    boxed_slice,
}