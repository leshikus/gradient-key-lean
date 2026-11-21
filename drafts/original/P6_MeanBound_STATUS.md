# P6 mean estimate of Lemma 4.3 — integration status

## Artifacts

- `P6_MeanBound.lean`: 367-line **candidate integration module**, importing the v4 `GradientKeySection4` source, with no sorry/admit/axiom/unsafe declarations. **NOT COMPILED**.
- `P6_sanity_check.py`: independent, exact-rational enumeration of the mathematical P6 coupling and bound for small parameters. **Not a formal proof**.

## Target and scope

Article, Section 4, Lemma 4.3: `V_i ≤ n/(n-i)` for `0 ≤ i < n`.
Here `n = k+1`. The uniform sample space is
`GradientKey.Concrete.Sample (k+1) m`, a valid distinct-column table
and an independent column index. The expected split imbalance is `V hn i`.

## New concrete definitions and declarations in P6

1. `deleteRow`: preserves the order of the `k` remaining rows (`Fin.succAbove`).
2. `deletedChoice`, `deletedStep`, `deletedCandidateAt`: deterministic greedy
   path on a row-deleted table, preserving first-in-order tie breaking;
   if all rows are constant, a non-singleton candidate set is a leaf.
3. `deletedCandidate_mem`, `deletedCandidate_nonempty`,
   `deletedStep_pairClosed`, `deletedCandidate_pairClosed`: candidate sets are
   nonempty, and contain both or neither members of every duplicated pair.
4. `testedBefore`, `active` (`E_r`), `rowDeletedCandidate`, `U`, `actual`, `V`.
5. `U_nonneg`: all row-deleted imbalances are nonnegative.
6. `fibre_sum_le_card`: the complete Lemma 4.2 *fibre* mean bound, including
   the empty-extension case, by the existing
   `RowDeletion.conditional_inserted_imbalance_le_one`.
7. `row_mean_le_one_of_P3`: averages the conditional fibre bound over `B,j`,
   assuming the explicit deletion/reinsertion equivalence and transport
   identity which P3 must prove. No rowwise moment inequality is assumed.
8. `pointwise_greedy_average_of_P1_P4`: proves the pointwise greedy
   comparison from P1's **exact `n-i` unused rows** and P4's `v_i ≤ U_r` on
   `E_r`, with separate handling of leaves.
9. `expectedImbalance_le_rows_of_P1_P3_P4`: instantiates the v4 generic
   `mean_imbalance_from_unused_rows` on the concrete sample space.

## Outstanding dependencies (DO NOT MISREPORT AS PROVED)

- **P1:** for every sample with a fork at depth `i`, prove
  `∑ r, (if active hn r ω i then (1:ℝ) else 0) = (k+1:ℝ) - (i:ℝ)`.
  The count is exact, not just `≥`.
- **P4:** for each active row `r`, prove `actual hn i ω ≤ U r i ω`.
  Use the fact that row `r` is not tested above `i`, so deleted and full
  candidate sets agree, and that the full greedy row minimizes imbalance
  among unused rows. Must use first-in-row-order ties.
- **P3:** for every `r`, construct a true equivalence
  `Sample (k+1) m ≃ Fibres k m` (`Fibres = (Σ B, Extension B) × Fin m`),
  and prove `U r i ω = fibreU i (fibreEquiv r ω)`.
  The fibre contains all valid inserted rows; the independent column `j`
  is not forgotten.
- **P0/integration:** provide a compiled `GradientKeySection4.lean` in the
  Lean import path and a nonempty sample type for the valid paper regime.

There is **not** yet an unconditional theorem named
`expectedImbalance_le_rows`. The conditional theorem's suffix deliberately
records the outstanding inputs. After discharging P1/P3/P4, give the final
unconditional theorem that reduces to
`expectedImbalance_le_rows_of_P1_P3_P4`.

## Verification / actual environment

Command attempted:

```
lake env lean /mnt/data/P6_MeanBound.lean
```

Output:

```
bash: line 1: lake: command not found
exit=127
```

`lean`, `lake`, and `elan` are all absent. Exact toolchain/Mathlib revisions
are therefore unavailable, and no Lean elaboration/typecheck claim is made.
The v4 baseline is itself marked uncompiled. Some Mathlib API or elaboration
fixes may be required in this candidate file once P0 supplies a project.

Independent small-case mathematical checks (`python P6_sanity_check.py`)
completed without assertion failures for `(n,m) = (1,2), (2,2), (2,3),
(2,4), (3,2), (3,3), (3,4)`, up to 6720 table-column samples for a case.
These checks do not verify Lean code or general theorems.

## Minimal merge plan

1. P0: compile/fix `GradientKeySection4.lean`; re-run `lake env lean
   P6_MeanBound.lean` in the same pinned Lean+Mathlib project.
2. P3: supply `fibreEquiv` and `fibreTransport` proofs matching the interfaces.
3. P1/P4: supply `unusedCount` and `greedyLower` for all `i < n`.
4. Combine these facts using `expectedImbalance_le_rows_of_P1_P3_P4` to
   publish the unconditional `expectedImbalance_le_rows` (no new assumptions).
5. Feed its result into the `hVMean` argument of the conditional v4
   Theorem 4.4; leave the separate Hoeffding-tail and transition tasks intact.

Nothing in this module alters the article or the baseline file.
