# Theorem 4.4 — Lean formalization progress (v4)

**Source:** `article.tex`, Section 4, Lemmas 4.1–4.3, and Theorem 4.4.

**Verification: UNCHECKED.** The runtime has no `lean`, `lake`, `elan`, or Mathlib installation. DNS/network access to Lean release servers also fails. The source therefore has **not been compiled**. No `sorry` or `axiom` declarations appear in the proposed source, but **there are substantial explicit hypotheses** and Lean elaboration/API issues may remain. Do not interpret the file as a complete proof.

## New in v4 (relative to v3)

The main advance is the **full mathematical mean calculation of Lemma 4.2**, with the conditioning represented by the finite type of admissible inserted rows. Its target statement is

`conditional_inserted_imbalance_exact`:

> For a deleted-row matrix `B`, a nonempty `S` containing complete equal-column classes of `B`, and a uniformly selected admissible inserted row `x`, the mean of `(s-2k)^2/s` is exactly `f/s`, where `f` is the number of unique columns in `S`.

This result no longer assumes fair/independent singleton bits. Instead, it derives the needed first and second moments by finite involution arguments:

- `flipBit_preserves_extension`: toggling the bit of a unique column leaves the set of valid inserted rows invariant.
- `flipExtension`: this toggle is a permutation of the finite type `Extension B`.
- `conditional_unique_sign_mean_zero` and `conditional_unique_sign_cross_zero`: sign reversal proves unbiased bits and vanishing cross-moments.
- `conditional_unique_signs_second_moment`: the exact free-sign second moment follows from the v3 pairwise-orthogonality lemma.
- `partner_twice`, `duplicate_sign_sum_zero`: an admissible extension forces every duplicated column to have a unique partner; on a pair-closed candidate set, opposite signs of duplicated columns cancel.
- `all_signs_eq_unique_signs`: signed imbalance depends only on the unique columns.
- `insertedImbalance_eq_signed`: converts the signed-sum expression into the article's exact `(s-2k)^2/s` definition.
- `conditional_inserted_imbalance_exact` and `conditional_inserted_imbalance_le_one`: equality `f/s` and the bound `≤ 1`.

Another new lemma, `mean_imbalance_from_unused_rows`, establishes **the finite averaging step of Lemma 4.3's first bound**, deriving `V_i ≤ n/(n-i)` from a pointwise greedy comparison and the rowwise estimates `E U_r ≤ 1`. Its premises still need to be connected to the concrete tree.

## Independent exact enumeration

`verify_row_deletion.py` checks the identity `E[(s-2k)^2/s | B] = f/s` for every feasible `B` in the following finite cases (all `S` that are nonempty and pair-closed):

| Remaining rows | Columns | Feasible deleted-row tables | Checked candidate sets |
|---:|---:|---:|---:|
| 0 | 2 | 1 | 1 |
| 1 | 3 | 6 | 18 |
| 1 | 4 | 6 | 18 |
| 2 | 4 | 204 | 1,476 |
| 2 | 5 | 600 | 6,120 |
| **Total** | | **817** | **7,633** |

All identities hold using exact rational arithmetic. The check is independent of Lean and does not establish Lean code correctness.

## Remaining formalization obligations

1. **Compilation:** compile and debug all ~1,730 lines in a matching Mathlib project. Some tactic syntax/API references may require revision. **Nothing in v4 is claimed compiler-verified.**
2. **Concrete greedy path:** prove every non-singleton set is split, no row is tested twice on a path, termination, and the path tail inequality `FinitePathData.pathTail`.
3. **Lemma 4.1 transition:** prove the finite expected candidate-size recurrence by summing over forks/candidate sets.
4. **Conditioning bridge:** define deletion/insertion for a selected row `r`, and identify the conditional distribution of its bits given the other rows with the uniform `Extension B` distribution. The v4 moment theorem applies once this bridge is made.
5. **Row-deleted candidate sets:** show `S_i^(-r)` are `PairClosed` and that the actual greedy path agrees with the row-deleted path on the event the tested row has not appeared above depth `i`.
6. **Lemma 4.3 mean:** apply `mean_imbalance_from_unused_rows` to the concrete samples. Its algebraic/finite-averaging part is now in v4.
7. **Hoeffding tail in Lemma 4.2 and the logarithmic Lemma 4.3 bound:** prove the conditional subGaussian tail `Pr(v_r(S)>z) ≤ 2 exp(-z/2)` from the independent fair free bits. Then prove the truncated-expectation bound and Jensen/concavity step used in Lemma 4.3.

Theorem 4.4 itself and parts (a)–(c) remain encoded conditionally, exactly as in earlier versions. v4's advances concern upstream mathematical obligations, not an unconditional final theorem.

## Running in a Mathlib project

```bash
lake env lean GradientKeySection4.lean
python verify_row_deletion.py
```

## Consulted Mathlib API references

- `Equiv.sum_comp` — sum reindexing by an equivalence.
- `Finset.sum_involution` — cancellation under a fixed-point-free involution.
- `Finset.sum_filter_add_sum_filter_not` — decomposition of a finite sum by a predicate.
- `Mathlib.Probability.Moments.SubGaussian` — possible Hoeffding/subGaussian infrastructure for the remaining tail estimate.
