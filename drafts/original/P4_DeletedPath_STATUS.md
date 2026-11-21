# P4 — Deleted-path coupling: implementation status

## Deliverables

- `P4_DeletedPath.lean` — isolated Lean 4 / Mathlib candidate, namespace
  `GradientKey.P4`. This file neither imports nor overwrites the uncompiled
  v4 baseline.
- `P4_regression.py` — executable *independent*, exact-rational tests for
  small valid and arbitrary binary tables; it is **not a proof of the Lean file**.

## Actual verification

**NOT COMPILED.** Command attempted in this execution environment:

```console
$ lake env lean /mnt/data/P4_DeletedPath.lean
bash: line 1: lake: command not found
# exit status 127
```

No `lean`, `lake`, or `elan` executable or local Mathlib checkout was found.
Consequently no Lean/Mathlib revision or compiler success can be reported.
The Lean source is candidate code and may require syntax, elaboration, and proof
repairs. Zero `sorry`, `admit`, `axiom`, or `unsafe` tactic/declaration holes
were found by a text check; this is NOT a substitute for compilation.

Independent Python run:

```console
$ python /mnt/data/P4_regression.py
PASS: 2134 valid tables, 39980 path states, 38836 row events; 5137 arbitrary tables (including duplicates)
```

The tests check selected-column survival, duplicate-class closure, prefix
candidate and available-row agreement, the event-conditioned `U_r` equality,
`n-i` available rows on forks, pointwise imbalance inequality (using exact
fractions), and terminal-state constancy.

## Main definitions / declarations (candidate, not compiler-verified)

| Name in `GradientKey.P4` | Meaning |
|---|---|
| `RemainingTable`, `SameColumn`, `PairClosed`, `deleteRow` | Row-deleted table, using the original indices restricted to `{k // k ≠ r}` |
| `firstMax`, `firstMax_filter_not`, `selectRow_erase` | First-maximum tie-breaking and stability when removing an unchosen row |
| `PathState`, `step`, `pathFrom` | Greedy path with candidate columns and available rows; stops without a split |
| `deletedCandidate`, `U` | `S_i^(-r)` and deleted-row split imbalance |
| `deletedCandidate_nonempty` | Every deleted candidate contains target `j` |
| `deletedCandidate_pairClosed` | Equal deleted columns stay together |
| `pathFrom_constant_after_stop` | After no splitting row exists, the entire state stays fixed |
| `prefixCoupling` | Agreement of both candidates and remaining-row sets when each preceding step avoids `r` |
| `Event`, `prefixAvoids_of_available`, `event_prefixCoupling`, `U_on_event` | Bridge from available row to the paper's `E_r` and equality `U_r = v_r(S_i)` |
| `selected_quality_max`, `rowImbalance_antitone` | First-max quality implies least split imbalance |
| `full_unused_card` | Exactly `n-i` unused rows assuming the first `i` steps split |
| `pointwise_greedy_comparison` | Pointwise `v_i <= sum_r (1_{E_r} U_r)/(n-i)` from P1 fork progress |

## Outstanding obligations and dependencies

1. **P0 compiler/setup:** Check this module in a pinned Lean 4 + Mathlib
   environment and repair syntax or API mismatches. Compile the v4 baseline
   separately; it currently cannot be safely imported.
2. **P1 full-path invariants:** For a full table with distinct columns, prove:
   - All stages before a fork at level `i` genuinely split (`hForks`).
   - If the current candidate size is `>= 2`, some available row has positive
     quality (`hCurrent`).
   - Removing previously tested rows from the pool of possible choices does not
     change the *paper's* greedy rule because those rows are constant on the
     current candidate set.
   These facts discharge the explicit P1 hypotheses in
   `event_prefixCoupling`, `full_unused_card`, and
   `pointwise_greedy_comparison`. Until then those are **conditional results**,
   not completed theorems for all valid tables.
3. **P3 / baseline type adapter:** Baseline
   `GradientKey.RowDeletion.RemainingTable (n-1) m` uses `Fin (n-1)` row
   indices; P4 deliberately uses the order-preserving subtype
   `{k : Fin n // k ≠ r}`. Construct the order-preserving equivalence
   `Fin (n-1) ≃o {k : Fin n // k ≠ r}` and prove the equality of
   `SameColumn` / `PairClosed` predicates under transport. This avoids any
   assumption that the deleted columns remain distinct and keeps original
   row-order tie-breaking.
4. **P6 mean bound:** Instantiate the existing finite-averaging lemma using
   `pointwise_greedy_comparison` after P1, use `U_on_event` and
   `deletedCandidate_pairClosed` to invoke the conditional fixed-row mean
   bound via P3.
5. **P7 tail bound:** Reuse the same event and deleted-row variables, then
   combine with P5's Hoeffding estimate.

## Minimal integration plan

1. Compile/fix `P4_DeletedPath.lean` standalone.
2. Add an adapter from the original-index row subtype to the baseline's
   `Fin (n-1)` representation, leaving the baseline unmodified until P0
   establishes a compiling version.
3. Import the module in P6/P7, obtain the `hForks`/`hCurrent` lemmas from P1,
   then instantiate `pointwise_greedy_comparison` and `U_on_event`.
4. Remove conditional P1 parameters *only after* a valid-table bridge has been
   proved; do not silently strengthen the model or change the paper's theorem.
