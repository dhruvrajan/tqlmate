# Stainless verification (tqlmate Scala prototype)

Verified subset: `verified/src/tqlmate/core/{Codes,Pure,Lemmas}.scala`.

## How to run

```bash
./alt/scala-stainless/scripts/verify.sh
# or with a preinstalled stainless:
STAINLESS_HOME=/path/to/stainless-dotty-standalone ./alt/scala-stainless/scripts/verify.sh
```

Pin: Stainless **0.10.3** (`stainless-dotty-standalone`).

## Results (this checkout)

See [`stainless-report.txt`](stainless-report.txt). Summary from the last local run:

| Metric | Value |
| --- | --- |
| VCs | **158 valid / 158 total** |
| Invalid | 0 |
| Unknown / timeout | 0 |
| `@extern` in verified sources | **none** |
| Solver time (warm cache) | ~0.1–0.5 s |
| Wall clock (compile + verify) | ~7 s |

## What is proved (mirrors Verus / Lean CoreProperties)

| Claim | Where |
| --- | --- |
| `bodyIsEmpty` / digit helpers terminate | `Codes.*` |
| `codesEq` ↔ structural `==` | `Codes.codesEq` ensures |
| ApplyUp nonempty ⇒ append version | `Pure.step` ensures |
| ApplyUp / ApplyDown empty ⇒ Err | `Pure.step` ensures |
| ApplyDown nonempty ⇒ `removeLastMatchingSpec` | `Pure.step` ensures |
| `run s [] = Ok s` | `Pure.run` ensures |
| Empty pending / empty files ⇒ empty migrate plan | `planUpsFromPending` / `planMigrate` ensures |
| Empty applied ⇒ empty rollback (∀ files) | `planRollback` ensures + `Lemmas.rollbackEmptyApplied` |
| `removeLastMatching` nil / singleton | `Lemmas.lemmaRemoveLastMatching*` |
| Empty → ApplyUp → ApplyDown → empty | `Lemmas.roundtripUpDown` |
| One ApplyUp appends | `Lemmas.runOneApplyUpAppends` |
| Fully applied ⇒ idempotent empty migrate | `Lemmas.migrateIdempotentWhenFullyApplied` |
| Pending filter empty when all applied | `Lemmas.pendingEmptyWhenAllApplied` |
| Ledger membership after ApplyUp | `Lemmas.applyUpRecordsVersion` (+ `versionInSnoc`) |

## Trusted / outside verification

Same story as Rust Verus/Lean:

1. **TypeDB effects** (`cli` Runner / Ledger) — axiomatized: successful schema tx ⇒ abstract `step` happened.
2. **String ↔ `List[BigInt]` bridge** (`cli/tqlmate/bridge`) — trusted encoding for the JVM CLI.
3. **Parse / split / slugify / filesystem / clap** — unverified CLI (Lean ExtrProperties still cover Rust parse fixtures).

## Deferred (honest gaps vs Verus/Lean)

- Full `run ↔ run_spec` fold for arbitrary plans (Verus also marks cons-fold as MISSING).
- `planMigrate` length ≡ pending count for arbitrary files (attempted; timed out — not claimed).
- Parse/split proofs (Stainless `String` is thin; codes lists cover the decision core).
