//! Parity between Rust `pure` helpers and ExtrProperties / CoreProperties Lean fixtures.
//!
//! Cases below match `native_decide` / `Result.reducesTo` examples in
//! `verification/lean/TqlmateExtract/{ExtrProperties,CoreProperties}.lean`.

use tqlmate::pure::{
    check_strict_order, dump_header, parse_version_name, plan_migrate, plan_rollback, run, slugify,
    split_up_down, step, strip_dump_header, MigrationId, MigrationSpec, Op, ParseError, PlanError,
    State, StepError, StrictOrderError, Version,
};

fn mid(version: &str, name: &str) -> MigrationId {
    MigrationId {
        version: Version::new(version),
        name: name.into(),
    }
}

fn mspec(version: &str, up: &str, down: &str) -> MigrationSpec {
    MigrationSpec {
        version: Version::new(version),
        name: version.into(),
        up: up.into(),
        down: down.into(),
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

/// CoreProperties: migrate pending / idempotent / rollback inverse / rejects.
#[test]
fn lean_core_plan_and_run() {
    let files = vec![
        mspec("1", "u1", "d1"),
        mspec("2", "u2", "d2"),
        mspec("3", "u3", "d3"),
    ];
    let plan = plan_migrate(&files, &[Version::new("1")], false).unwrap();
    assert_eq!(plan.len(), 2);
    let next = run(State::new(vec![Version::new("1")]), &plan).unwrap();
    assert_eq!(
        next.applied,
        vec![Version::new("1"), Version::new("2"), Version::new("3")]
    );
    assert!(plan_migrate(&files, &next.applied, false)
        .unwrap()
        .is_empty());

    assert!(matches!(
        plan_migrate(&[mspec("1", "", "d")], &[], false),
        Err(PlanError::EmptyUp(_))
    ));
    assert!(matches!(
        plan_migrate(&files, &[Version::new("1"), Version::new("3")], true),
        Err(PlanError::StrictOrder { .. })
    ));
    assert!(plan_rollback(&files, &[]).unwrap().is_empty());
    assert!(matches!(
        plan_rollback(&[], &[Version::new("9")]),
        Err(PlanError::MissingFile(_))
    ));

    let s1 = step(
        State::empty(),
        Op::ApplyUp {
            version: Version::new("1"),
            up: "u1".into(),
        },
    )
    .unwrap();
    let down = plan_rollback(&files, &s1.applied).unwrap();
    assert_eq!(run(s1, &down).unwrap().applied, Vec::<Version>::new());

    assert!(matches!(
        step(
            State::empty(),
            Op::ApplyUp {
                version: Version::new("1"),
                up: "".into(),
            }
        ),
        Err(StepError::EmptyUp(_))
    ));
}
