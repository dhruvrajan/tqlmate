//! Parity between Rust `pure` helpers and ExtrProperties Lean fixtures.
//!
//! Each case below matches a `native_decide` / `Result.reducesTo` example in
//! `verification/lean/TqlmateExtract/ExtrProperties.lean`. Keep them in sync.

use tqlmate::pure::{
    check_strict_order, dump_header, parse_version_name, slugify, split_up_down, strip_dump_header,
    MigrationId, ParseError, StrictOrderError, Version,
};

fn mid(version: &str, name: &str) -> MigrationId {
    MigrationId {
        version: Version::new(version),
        name: name.into(),
    }
}

/// `parse_ok_example` / `parse_rejects_*` in ExtrProperties.lean
#[test]
fn lean_parse_examples() {
    assert_eq!(
        parse_version_name("20240101120000_create_person.tql").unwrap(),
        (Version::new("20240101120000"), "create_person".into())
    );
    assert_eq!(
        parse_version_name("abc_name.tql"),
        Err(ParseError::VersionDigits)
    );
    assert_eq!(parse_version_name("123_.tql"), Err(ParseError::Name));
    assert_eq!(parse_version_name("nope.tql"), Err(ParseError::Filename));
    assert_eq!(
        parse_version_name("123_name.sql"),
        Err(ParseError::Extension)
    );
}

/// `split_ok_example` / `split_ok_case_insensitive` / `split_rejects_*`
#[test]
fn lean_split_examples() {
    assert_eq!(
        split_up_down("-- migrate:up\ndefine x;\n-- migrate:down\nundefine x;\n").unwrap(),
        ("define x;".into(), "undefine x;".into())
    );
    assert_eq!(
        split_up_down("-- MIGRATE:UP\ndefine x;\n-- Migrate:Down\nundefine x;\n").unwrap(),
        ("define x;".into(), "undefine x;".into())
    );
    assert_eq!(split_up_down("no markers here"), Err(ParseError::Markers));
    assert_eq!(split_up_down(""), Err(ParseError::Markers));
}

/// `strict_order_detects_hole` / `strict_order_ok_prefix` / empty-applied theorem
#[test]
fn lean_strict_order_examples() {
    let files = vec![mid("1", "a"), mid("2", "b"), mid("3", "c")];
    assert!(matches!(
        check_strict_order(&files, &[Version::new("1"), Version::new("3")]),
        Err(StrictOrderError::OutOfOrder {
            pending,
            applied_up_to,
        }) if pending.as_str() == "2" && applied_up_to.as_str() == "3"
    ));
    assert!(check_strict_order(&files, &[Version::new("1"), Version::new("2")]).is_ok());
    assert!(check_strict_order(&files, &[]).is_ok());
}

/// `slugify_examples`
#[test]
fn lean_slugify_examples() {
    assert_eq!(slugify("Create Person"), "create_person");
    assert_eq!(slugify("!!!"), "migration");
    assert_eq!(slugify("a__b"), "a_b");
}

/// `dump_strip_roundtrip`
#[test]
fn lean_dump_strip_roundtrip() {
    let files = [mid("1", "person")];
    let h = dump_header(&[Version::new("1")], &files);
    assert_eq!(
        h,
        "-- Schema dumped by tqlmate\n-- Applied migrations:\n--   1_person\n\n"
    );
    assert_eq!(
        strip_dump_header(&format!("{h}define\n  entity x;")),
        "define\n  entity x;"
    );
}
