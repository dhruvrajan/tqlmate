# Verus verification (migrate / rollback core)

Machine-checked properties of a **Verus-annotated Rust** encoding of the pure
migrate/rollback algorithm (same class of claims as Lean
`CoreProperties.lean`). Production runtime still uses `src/pure.rs`; this crate
is the verified executable model of that core, not a ghost-only Spec twin.

```bash
# from repo root (downloads Verus on Linux x86_64 if needed)
./verification/scripts/verify-verus.sh
```

Or directly:

```bash
verus --crate-type=lib verification/verus/src/lib.rs --rlimit 80
```

Pin: see `verification/VERSIONS` (`verus=`).

## What Verus proves

| Claim | Where |
| --- | --- |
| `body_is_empty` ↔ whitespace-only view | `body_is_empty` ensures |
| `run s [] = Ok s` (views) | `run` ensures |
| Spec fold `run_spec` (mathematical interpreter) | `run_spec` |
| ApplyUp nonempty ⇒ append version view | `step` ensures |
| ApplyUp / ApplyDown empty ⇒ Err | `step` ensures |
| ApplyDown nonempty ⇒ `remove_last_matching_spec` | `step` ensures |
| `remove_last_matching` matches recursive spec | `remove_last_matching` ensures |
| `remove_last_matching []` / singleton lemmas | `lemma_remove_last_matching_*` |
| Empty applied ⇒ empty rollback (∀ files) | `plan_rollback` ensures |
| Empty pending ⇒ empty ups plan | `plan_ups_from_pending` ensures |
| Empty files + nonstrict ⇒ empty migrate plan | `plan_migrate` ensures |
| Nonstrict migrate = pending ≫ ups | by construction in `plan_migrate` |
| Empty → ApplyUp → ApplyDown → empty | `roundtrip_up_down` |
| One ApplyUp appends version | `run_one_apply_up_appends` |

## Assumptions / MISSING (honest)

1. **ASCII bodies** — `requires s.is_ascii()` on up/down emptiness (production
   `pure.rs` checks bytes; TypeQL migrations are ASCII in practice).
2. **`version_str_lt`** — `#[verifier::external_body]`; Rust `str` `<` is
   assumed equal to `seq_char_lt` on views (strict-order only).
3. **`run` cons fold** — `run` is recursive like production; ensures currently
   lock the **nil** case. Cons behavior is covered by `step` + `run_spec` +
   recursion structure; a full `run ↔ run_spec` postcondition for arbitrary
   plans is **MISSING** (deferred, not silently claimed).
4. **Parse / split / slugify** — not in this crate (still Lean
   `ExtrProperties` + Rust `tests/spec_parity.rs`).
5. **TypeDB effects** — trusted at the runner boundary (same story as Lean).

## Relation to `src/pure.rs`

| | Production `src/pure.rs` | Verus `verification/verus` |
| --- | --- | --- |
| Role | Runtime + Aeneas extract | Verified annotated Rust |
| Style | Aeneas-friendly loops / recursion | Verus `ensures` / `decreases` |
| Checked by | unit tests + Lean extract proofs | `verus` |

Keep them aligned when changing migrate/rollback semantics; extend
`src/pure.rs` tests and this crate’s ensures together.

## TypeDB / effects (trusted)

Unchanged from the Lean story: `src/runner.rs` `execute_plan` is the effect
oracle. Verus does **not** prove TypeDB transactions.
