use expect_test::expect;

use super::check_infer;

#[test]
fn opaque_generics() {
    check_infer(
        r#"
//- minicore: iterator
pub struct Grid {}

impl<'a> IntoIterator for &'a Grid {
    type Item = &'a ();

    type IntoIter = impl Iterator<Item = &'a ()>;

    fn into_iter(self) -> Self::IntoIter {
    }
}
    "#,
        expect![[r#"
            150..154 'self': &'a Grid
            174..181 '{     }': impl Iterator<Item = &'a ()>
        "#]],
    );
}

#[test]
fn foobar() {
    check_infer(
        r#"
//- minicore: iterators

struct TyLoweringContext<'db, 'a>;
struct PathLoweringContext<'a, 'b, 'db>;

impl<'a, 'b, 'db> PathLoweringContext<'a, 'b, 'db> {
    fn new(
        ctx: &'a mut TyLoweringContext<'db, 'b>
    ) -> Self {
        loop {}
    }

    fn assoc_type_bindings_from_type_bound<'c>(
        mut self,
        trait_ref: TraitRef<'db>,
    ) -> Option<impl Iterator<Item = Clause<'db>> + use<'a, 'b, 'c, 'db>> {
        Some([[Clause::<'db>::new()]].iter().flat_map(|it| it))
    }
}

impl<'db, 'a> TyLoweringContext<'db, 'a> {
    fn lower_type_bound<'b>(
        &'b mut self,
        bound: &'b TypeBound,
    ) -> impl Iterator<Item = Clause<'db>> + use<'b, 'a, 'db> {
        let x = PathLoweringContext::new(self).assoc_type_binding_from_type_bound(TraitRef::<'db>::new());
        [Clause::<'db>::new()].into_iter().chain(x.into_iter().flatten())
    }
}

struct TypeBound;
struct Ty<'db>;
struct Clause<'db>;

impl Clause<'db> {
    fn new() -> Self {
        loop {}
    }
}

struct TraitRef<'db>;

impl TraitRef<'db> {
    fn new() -> Self{
        loop {}
    }
}

fn foo<'db, 'a>(mut x: TyLoweringContext<'db, 'a>) {
    let mut a = None;
    for pred in x.lower_type_bound(&TypeBound) {
        a = Some(pred);
    };
}
"#,
        expect![[]],
    );
}
