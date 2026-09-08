# Formal verification (Aeneas + Lean 4)

Scope: the **pure** migration/ledger algorithm in [`src/pure.rs`](../src/pure.rs)
(version parsing, up/down split, status / strict-order, slugify, dump header).
No TypeDB driver, async, or filesystem I/O.

## End-to-end claim (what CI checks)

```
src/pure.rs  →  Charon  →  Aeneas  →  lean/aeneas-generated/{Types,Funs}.lean
                                              ↓
                                    lake build (imports Aeneas + Funs)
                                              ↓
                         ExtrProperties theorems about extracted `pure.*`
```

| Layer | Artefact | CI / `lake build` |
|-------|----------|-------------------|
| **Extraction** | Charon + Aeneas → [`lean/aeneas-generated/`](lean/aeneas-generated/) | **Elaborated.** `TqlmateExtract` imports `Types` + `Funs` + filled `FunsExternal`. Deleting/breaking `Funs.lean` fails the build. Marked `linguist-generated`. |
| **Externals** | [`TqlmateExtract/FunsExternal.lean`](lean/TqlmateExtract/FunsExternal.lean) | Hand-filled models for std holes Aeneas left open (`str`/`String`/ranges). Not regenerated. |
| **Extracted proofs** | [`ExtrProperties.lean`](lean/TqlmateExtract/ExtrProperties.lean) | **Machine-checked properties of extracted `tqlmate_extract.pure.*`.** |
| **Spec (readable twin)** | [`Spec.lean`](lean/TqlmateExtract/Spec.lean) + [`Properties.lean`](lean/TqlmateExtract/Properties.lean) | Still built. Same concrete fixtures as ExtrProperties / Rust parity; Spec is the readable model, ExtrProperties closes the Spec↔extract gap for those fixtures. |

Release / `cargo build --release` never depends on Lean, Charon, or Aeneas.

## Parity with Rust

[`tests/spec_parity.rs`](../tests/spec_parity.rs) locks the same concrete vectors used in Spec
`Properties` and ExtrProperties (`parse_*`, `split_*`, `strict_order_*`, `slugify_*`, …)
to `src/pure.rs` outputs.

```bash
cargo test --no-default-features --test spec_parity
```

## Toolchain

| Component | Version |
|-----------|---------|
| Lean 4 | `leanprover/lean4:v4.31.0` ([`lean/lean-toolchain`](lean/lean-toolchain)) |
| Aeneas | `33e3b2b4a5b7fa734fe8bb1282ebad066b38d049` (Lake `require` + extract pin) |
| Charon | `f0785b40f11dabae831fad31f819a473f19e4dfb` |

See [`VERSIONS`](VERSIONS). Lake pulls Aeneas’s Lean package from GitHub (`backends/lean`, brings Mathlib).

## Extracted theorems (`ExtrProperties`)

Proved about **Aeneas `Funs`** (via `Result.reducesTo` / `native_decide`):

| Theorem | Meaning |
|---------|---------|
| `parse_rejects_*_example` / `parse_ok_example` | Filename parse reject/ok on extracted `parse_version_name` |
| `split_rejects_*` / `split_ok_*` | Marker split on extracted `split_up_down` |
| `strict_order_detects_hole` / `strict_order_ok_prefix` / `check_strict_order_empty_applied` | Extracted `check_strict_order` |
| `pending_applied_disjoint_example` | Extracted `pending_applied_disjoint` |
| `slugify_examples` | Extracted `slugify` |

Spec `Properties` keeps the same fixture table plus a general Spec-level
`pending_applied_disjoint` proof.

## Reproduce

```bash
# elan: https://lean-lang.org/lean4/doc/setup.html
cd verification/lean
lake update
lake exe cache get   # Mathlib oleans
lake build
```

### Re-extract

```bash
./verification/scripts/extract-aeneas.sh
```

Post-extract, the script patches `PartialOrd.*.default` calls to pass `.partial_cmp`
(Aeneas Lean models expect the field, not the whole trait value) and refreshes
symlinks `TqlmateExtract/{Types,Funs}.lean` → `aeneas-generated/`.
