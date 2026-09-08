//! Unit tests: ledger / dump TypeQL strings and shipped ledger migration planning (no Docker / TypeDB).

use std::path::PathBuf;

use tqlmate::{
    bootstrap_schema, dump_header, is_ledger_version, plan_ledger_ensure, record_delete,
    record_insert, shipped_ledger_migrations, strip_dump_header, LedgerEnsureAction, MigrationFile,
    Version, ATTR_APPLIED_AT, ATTR_VERSION, ENTITY, LEDGER_VERSION_LEN, LEDGER_VERSION_PREFIX,
};

fn mf(version: &str, name: &str, up: &str, down: &str) -> MigrationFile {
    MigrationFile {
        version: Version::new(version),
        name: name.into(),
        path: PathBuf::from(format!("{version}_{name}.tql")),
        up: up.into(),
        down: down.into(),
    }
}

#[test]
fn ledger_typeql_insert_delete() {
    let v = Version::new("20240101120000");
    assert_eq!(
        record_insert(&v, "2024-01-01T12:00:00"),
        format!(
            "insert $_ isa {ENTITY}, has {ATTR_VERSION} \"20240101120000\", has {ATTR_APPLIED_AT} 2024-01-01T12:00:00;"
        )
    );
    assert_eq!(
        record_delete(&v),
        format!("match $m isa {ENTITY}, has {ATTR_VERSION} \"20240101120000\"; delete $m;")
    );
}

#[test]
fn bootstrap_schema_defines_ledger_types() {
    let schema = bootstrap_schema();
    assert!(schema.contains(ENTITY));
    assert!(schema.contains(ATTR_VERSION));
    assert!(schema.contains(ATTR_APPLIED_AT));
    assert!(schema.contains("@card(1)"));
    assert!(schema.trim_start().starts_with("define"));
}

#[test]
fn shipped_ledger_migrations_list_embedded_init() {
    let files = shipped_ledger_migrations().expect("shipped");
    assert!(!files.is_empty(), "binary must embed at least ledger_init");
    assert_eq!(files[0].version.as_str(), "00000000000001");
    assert_eq!(files[0].name, "ledger_init");
    assert!(files[0].path.to_string_lossy().starts_with("embedded:"));
    assert!(files[0].up.contains(ENTITY));
    assert!(
        !files[0].down.trim().is_empty(),
        "empty down is a hard error"
    );
    for f in &files {
        assert!(
            is_ledger_version(&f.version),
            "{} must be reserved ledger version",
            f.version
        );
        assert_eq!(f.version.as_str().len(), LEDGER_VERSION_LEN);
        assert!(f.version.as_str().starts_with(LEDGER_VERSION_PREFIX));
    }
}

#[test]
fn is_ledger_version_reserved_range() {
    assert!(is_ledger_version(&Version::new("00000000000001")));
    assert!(is_ledger_version(&Version::new("00000000999999")));
    assert!(!is_ledger_version(&Version::new("20240101120000")));
    assert!(!is_ledger_version(&Version::new("1")));
    assert!(!is_ledger_version(&Version::new("0000000000001"))); // 13 digits
    assert!(!is_ledger_version(&Version::new("00000001000000"))); // only seven leading zeros
}

#[test]
fn plan_applies_all_on_fresh_database() {
    let shipped = shipped_ledger_migrations().unwrap();
    let plan = plan_ledger_ensure(&shipped, None);
    assert_eq!(
        plan,
        shipped
            .iter()
            .map(|m| LedgerEnsureAction::Apply(m.version.clone()))
            .collect::<Vec<_>>()
    );
}

#[test]
fn plan_idempotent_when_all_applied() {
    let shipped = shipped_ledger_migrations().unwrap();
    let applied: Vec<_> = shipped.iter().map(|m| m.version.clone()).collect();
    let plan = plan_ledger_ensure(&shipped, Some(&applied));
    assert!(
        plan.is_empty(),
        "ensure must be a no-op when already applied"
    );
}

#[test]
fn plan_stamps_legacy_bootstrap_then_applies_newer() {
    let v1 = mf(
        "00000000000001",
        "ledger_init",
        "define\n  entity _tqlmate_schema_migration;",
        "undefine\n  _tqlmate_schema_migration;",
    );
    let v2 = mf(
        "00000000000002",
        "ledger_extra",
        "define\n  attribute _tqlmate_note, value string;",
        "undefine\n  _tqlmate_note;",
    );
    let shipped = vec![v1, v2];

    // Pre-migration DB: types exist, no ledger versions recorded → stamp v1, apply v2.
    let plan = plan_ledger_ensure(&shipped, Some(&[]));
    assert_eq!(
        plan,
        vec![
            LedgerEnsureAction::Stamp(Version::new("00000000000001")),
            LedgerEnsureAction::Apply(Version::new("00000000000002")),
        ]
    );

    // Upgrade from v1-only ledger to v1+v2.
    let plan = plan_ledger_ensure(&shipped, Some(&[Version::new("00000000000001")]));
    assert_eq!(
        plan,
        vec![LedgerEnsureAction::Apply(Version::new("00000000000002"))]
    );
}

#[test]
fn plan_applies_non_init_even_when_first_pending() {
    // Types exist but only a post-init ledger migration is pending → must Apply, not Stamp.
    let shipped = vec![mf(
        "00000000000002",
        "ledger_extra",
        "define attribute _tqlmate_note, value string;",
        "undefine _tqlmate_note;",
    )];
    let plan = plan_ledger_ensure(&shipped, Some(&[]));
    assert_eq!(
        plan,
        vec![LedgerEnsureAction::Apply(Version::new("00000000000002"))]
    );
}

#[test]
fn plan_ordering_applies_pending_in_shipped_order() {
    let shipped = vec![
        mf("00000000000001", "a", "define entity a;", "undefine a;"),
        mf("00000000000002", "b", "define entity b;", "undefine b;"),
        mf("00000000000003", "c", "define entity c;", "undefine c;"),
    ];
    let plan = plan_ledger_ensure(&shipped, None);
    assert_eq!(
        plan.iter()
            .map(|a| match a {
                LedgerEnsureAction::Apply(v) | LedgerEnsureAction::Stamp(v) => v.as_str(),
            })
            .collect::<Vec<_>>(),
        vec!["00000000000001", "00000000000002", "00000000000003"]
    );
}

#[test]
fn dump_header_lists_labels_or_raw_versions() {
    let files = [MigrationFile {
        version: Version::new("1"),
        name: "person".into(),
        path: PathBuf::from("1_person.tql"),
        up: String::new(),
        down: String::new(),
    }];
    let empty = dump_header(&[], &files);
    assert!(empty.contains("-- Schema dumped by tqlmate"));
    assert!(empty.contains("--   (none)"));
    assert!(empty.ends_with('\n'));

    let with = dump_header(&[Version::new("1"), Version::new("99")], &files);
    assert!(with.contains("--   1_person\n"));
    assert!(with.contains("--   99\n"));
}

#[test]
fn strip_dump_header_removes_comment_preamble() {
    let text =
        "-- Schema dumped by tqlmate\n-- Applied migrations:\n--   1_person\n\ndefine\n  entity x;\n";
    assert_eq!(strip_dump_header(text), "define\n  entity x;");
    assert_eq!(strip_dump_header("define entity y;"), "define entity y;");
    assert_eq!(strip_dump_header("-- only comments\n\n"), "");
}

#[test]
fn dump_header_round_trip_with_strip() {
    let files = [MigrationFile {
        version: Version::new("20240101000000"),
        name: "person".into(),
        path: PathBuf::from("20240101000000_person.tql"),
        up: String::new(),
        down: String::new(),
    }];
    let header = dump_header(&[Version::new("20240101000000")], &files);
    let full = format!("{header}define\n  entity person;\n");
    assert_eq!(strip_dump_header(&full), "define\n  entity person;");
    assert!(bootstrap_schema().contains(ENTITY));
}
