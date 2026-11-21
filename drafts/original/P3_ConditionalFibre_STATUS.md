# P3 — Conditional fibre bridge: hand-off

**Status: NOT COMPILED / NOT LEAN VERIFIED.** No pinned Lean 4 + Mathlib
project or `lake`, `lean`, or `elan` executable is available in this runtime.
The imported `GradientKeySection4.lean` v4 source was readable as a Project
file, but the original bytes could not be materialized into the container;
its own progress document also describes it as uncompiled. Therefore all
Lean declarations below have **source-draft**, not compiler-verified status.
The exhaustive Python check is independent of the Lean elaborator.

## Delivered files

- `P3_FiniteFibreCore.lean`: imports only `Mathlib`; defines public
  `uniformMean`, a generic fibre equivalence, exact sum/cardinality and
  normalized tower identities, and transfers finite conditional mean and
  indicator-tail bounds, with guards for positive-cardinality fibres.
- `P3_ConditionalFibre.lean`: imports the v4 baseline and the core; uses
  `Fin.removeNth`/`Fin.insertNth` to recover the missing row at its exact
  original index and to prove the valid-table fibre equivalences.
  Proposes exact counting identities for the uniform `(A,j)` sample and
  corollaries applying the baseline's conditional mean theorem.
- `P3_verify_fibres.py`: independently exhaustive small-case check.

## Important theorem declarations (all: drafted, uncompiled)

| File | Declarations | Status |
| --- | --- | --- |
| Core | `FiniteFibre.sigmaEquiv`, `sum_over_fibres`, `card_over_fibres`, `tower_sum` | Draft |
| Core | `bound_from_fibre_sums`, `bound_from_positive_fibre_means`, `tail_from_positive_fibre_tails` | Draft |
| P3 | `deleteRow_insertRow`, `insertRow_deleteRow`, `insertRow_at`, `insertRow_other` | Draft |
| P3 | `distinct_insertRow_iff`, `tableFibreEquiv`, `table_fibre_feasible_iff`, `table_fibre_card` | Draft |
| P3 | `sample_card_factor`, `sampleFibreEquiv`, `sample_fibre_card`, `conditional_sample_mean_eq_extension`, `conditional_inserted_row_uniform` | Draft |
| P3 | `conditional_sample_imbalance_exact`, `unconditional_row_mean_le_one` | Draft; depends on v4 conditional moments |
| P3 | `unconditional_row_tail_of_extension_tails` | Draft *conditional transfer*; P5 must discharge its `hTail` parameter |

The source has no `sorry`, `admit`, `axiom`, or `unsafe` declarations. This
is a **syntax/text inspection**, not evidence of Lean correctness. The
last tail theorem is deliberately conditional; it is not a Hoeffding proof.

## Actual tests and errors

Attempted (from `/mnt/data`):

```text
$ lake env lean P3_ConditionalFibre.lean
bash: line 2: lake: command not found
exit_status=127
```

No toolchain revision can be reported: **none is installed**. Neither
`P3_FiniteFibreCore.lean` nor the imported v4 baseline has been compiled.

Mathematical cross-check:

```text
$ python P3_verify_fibres.py
(remaining rows, columns) = (0,2), (0,3), (1,3), (1,4), (2,4), (2,5)
All checked valid full-table fibres coincide exactly with admissible inserted
rows, for every insertion index and every fixed sampled column.
PASS (exhaustive finite checks; Lean NOT COMPILED)
```

Notably the enumeration includes 0-extension fibres and duplicate-column
row-deleted tables; it does not use an assumption that `B` is a valid table.

## Dependencies and minimal merge plan

1. **P0** pins the Lean/Mathlib project, gets `GradientKeySection4.lean`
   compiling, and either exports `GradientKey.finiteAverage` (currently
   `private` at roughly line 713) or accepts this module's public,
   definitionally identical `P3.uniformMean`. Exporting only the finite-
   average function and its needed linearity/monotonicity lemmas is a local
   API change, not a change to the mathematical statements.
2. Put both `.lean` files next to `GradientKeySection4.lean` (or under the
   corresponding module path) and compile in order:
   `lake env lean P3_FiniteFibreCore.lean`, then
   `lake env lean P3_ConditionalFibre.lean`. Debug the source against the
   actual pinned Mathlib API and report errors rather than weakening goals.
3. **Candidate-set agent:** provide a total function
   `candidate : RemainingTable n m → Fin m → Finset (Fin m)` representing
   `S_i^(-r)`, and prove `0 < (candidate B j).card` and
   `PairClosed B (candidate B j)` for every feasible `B`. This instantiates
   `unconditional_row_mean_le_one`, identifying the original `U_r`.
4. **P5:** instantiate `hTail` in
   `unconditional_row_tail_of_extension_tails` with the fixed-extension
   Hoeffding bound `2 * Real.exp (-z / 2)` for `z>0`. This is not done here.
5. **P6 / P10:** connect the resulting `E[U_r] ≤ 1` and tail estimates to
   the concrete `mean_imbalance_from_unused_rows` theorem and to the second
   Lemma 4.3 bound. The candidate-set coincidence on `E_r`, first-row tie
   breaking, and original path termination still need separate proofs.

No shared baseline source was modified. The paper's choice of row order and
its allowance of duplicate columns after deletion are preserved.
