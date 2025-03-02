use rustc_hash::FxHashMap;
use span::Span;
use syntax::{ast, AstNode};
use test_utils::extract_annotations;
use tt::{buffer::Cursor, Leaf, Punct, Spacing};

use crate::{
    dummy_test_span_utils::{DummyTestSpanMap, DUMMY},
    syntax_node_to_token_tree, DocCommentDesugarMode,
};

fn check_punct_spacing(fixture: &str) {
    let source_file = ast::SourceFile::parse(fixture, span::Edition::CURRENT).ok().unwrap();
    let subtree = syntax_node_to_token_tree(
        source_file.syntax(),
        DummyTestSpanMap,
        DUMMY,
        DocCommentDesugarMode::Mbe,
    );
    let mut annotations: FxHashMap<_, _> = extract_annotations(fixture)
        .into_iter()
        .map(|(range, annotation)| {
            let spacing = match annotation.as_str() {
                "Alone" => Spacing::Alone,
                "Joint" => Spacing::Joint,
                a => panic!("unknown annotation: {a}"),
            };
            (range, spacing)
        })
        .collect();

    let mut cursor = Cursor::new(&subtree.0);
    while !cursor.eof() {
        while let Some(token_tree) = cursor.token_tree() {
            if let tt::TokenTree::Leaf(Leaf::Punct(Punct {
                spacing,
                span: Span { range, .. },
                ..
            })) = token_tree
            {
                if let Some(expected) = annotations.remove(range) {
                    assert_eq!(expected, *spacing);
                }
            }
            cursor.bump();
        }
        cursor.bump_or_end();
    }

    assert!(annotations.is_empty(), "unchecked annotations: {annotations:?}");
}

#[test]
fn punct_spacing() {
    check_punct_spacing(
        r#"
fn main() {
    0+0;
   //^ Alone
    0+(0);
   //^ Alone
    0<=0;
   //^ Joint
   // ^ Alone
    0<=(0);
   // ^ Alone
    a=0;
   //^ Alone
    a=(0);
   //^ Alone
    a+=0;
   //^ Joint
   // ^ Alone
    a+=(0);
   // ^ Alone
    a&&b;
   //^ Joint
   // ^ Alone
    a&&(b);
   // ^ Alone
    foo::bar;
   //  ^ Joint
   //   ^ Alone
    use foo::{bar,baz,};
   //       ^ Alone
   //            ^ Alone
   //                ^ Alone
    struct Struct<'a> {};
   //            ^ Joint
   //             ^ Joint
    Struct::<0>;
   //       ^ Alone
    Struct::<{0}>;
   //       ^ Alone
    ;;
  //^ Joint
  // ^ Alone
}
        "#,
    );
}
