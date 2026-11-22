# Formalization status

Lean `v4.36.0`, Mathlib `v4.36.0`. `lake build` exits with 0. No `sorry`, `admit`, `axiom`, `unsafe` or
`native_decide` in `Section3/*.lean` or `Section4/*.lean`. Every final theorem below depends only on `propext`,
`Classical.choice`, `Quot.sound` (`logs/check3.log`, `logs/check.log`). CI runs both checkers and
`ci/check_proofs.py`: no proof shortcuts outside comments, every module a Lake root, and an axiom report with only
these three axioms for every theorem in `ci/expected_theorems.txt`.

The model is the article's: `Table n m = Fin n → Fin m → Bool`, `DistinctColumns`, `greedyRow` = the first row of
largest quality `min(k, s-k)`, `leafDepth` = number of forks on the path of a column, `cost = (1/m) ∑_j L_j`,
`tG n m = t_{n,m}(G)` (average over `𝒜_{n,m}`), `completeCost m = C(m) = ℓ + 2 - 2^{ℓ+1}/m`.

| Article | Lean | Status |
|---|---|---|
| Proposition 3.1 (`prop:path-formula`) | in progress. Verified steps: Möbius inversion `mobius_injective`; `tG_eq_forkTableCounts` (`tG` as a sum of fork counts); `pathCandidates_step_ssubset`, `pathFork_size_budget` (path shape, `d < n`); `pathOneStepTest_iff` (one greedy step with tie-breaking); `mobius_table_indicator`, `card_valid_with_row_constraints`, `fixedPath_card_factor`, `fixedPath_mobius_factor` (Möbius step and row factorization for fixed candidate sets and `ρ`); `pathChainOfFork_sizes`; definitions of chains, `c(λ)`, `W`, `V`, `F_n` and the right-hand side (`PathDefs`); `candidateAt_of_rowwise`, `rowwise_of_candidateAt`, `rowwise_unique` (rowwise conditions ⇔ the actual greedy path, unique schedule), `path_indicator_eq_sum`, `card_path_eq` (number of valid tables with given candidate sets = ∑_ρ ∑_π μ(π) ∏_rows counts) (`PathEvent`); `cell_sep`, `distinct_iff_cells`, `distinct_indicator_cells`, `card_path_cells` (the tested row at depth `k` separates cell `k` from later cells, so distinct columns = distinct within each cell; Möbius inversion in each cell, so blocks meeting two cells never occur) (`PathCells`); `coef_rec` (the article's `c(λ)` satisfies the recurrence of adding a singleton or enlarging a block) (`PathCoeff`); `tsum_rec`, `tsum_eq_coef`, `sum_mu_by_type` (the sum of `μ(π)` over the set partitions of type `λ` is `c(λ)`, so a Möbius sum of a function of the type is `∑_λ c(λ) F(λ)`) (`PathCoeff2`). Open: blocks crossing cells (now avoided), count of candidate-set families, per-chain identity, the formula, pruning, (3,4) checks | not yet formalized |
| Proposition 3.2 (`prop:small-m`): `t - C(m) = N_m(n)/(2^n)_m`, `N_m(n) = ∑_{j=1}^M a_j (2j)^n` | `prop_small_m` (`Section3/SmallM.lean`) | verified |
| — `B_k ≥ 0`, `B_M = 0`, all `B_k = 0` for `m ≤ 3`, `B_{m-1} > 0` for `m ≥ 4`, `M = 2^{m-1}` | `Bint_nonneg`, `Bint_numTypes`, `Bint_small`, `Bint_comb`, `numTypes_eq` | verified |
| — `m - 1 ≤ J < M`, `a_J = B_J/J! > 0` | `J_bounds`, `coeffA_J` | verified |
| — `N_m(n) = 2^n ∑_k B_k S(n,k)`; `k! S(n,k) = ∑_j (-1)^{k-j} C(k,j) j^n` | `prop32_stirling_form`, `prop32_stirling_identity` (`Section3/SmallItems.lean`) | verified |
| — `B_k = ∑_{T ∈ 𝒯_k} (L̄(G(T)) - C(m))` (`T : Fin k ↪ Ty`, `G(T)` on `tblOf T`), `k ≥ 1` | `Bk_eq_tuple_sum` | verified |
| Computation paragraph: `N_m(n) = 0` for `n ≥ 1`, `2^n < m` | `numer_eq_zero_of_two_pow_lt` | verified |
| Computation paragraph: `N_m(0) = 0`, via `∑_k (-1)^k B_k/k! = 0` (constant row type inserted) | `numer_zero`, `alt_sum_Bint` (`Section3/NumerZero.lean`) | verified |
| Examples: `t_{n,2^n} = n`, `t_{1,2} = 1`, `t_{n,2} = 1`, `t_{3,4} = 3408/1680`, `t_{4,11} - C(11) = 1/3003`, `t_{4,10} - C(10) = 18/5005` | `example_full`, `example_n1_m2`, `example_m2`, `example_n3_m4`, `example_n4_m11`, `example_n4_m10` (`Section3/Examples.lean`) | verified |
| Corollary 3.3 (`cor:exp`), with explicit `C`, `N₀` | `cor_exp` (`Section3/Asymptotic.lean`) | verified |
| Result 3, `m ≤ 3`: excess `0` | `excess_small` | verified |
| Proposition 3.4 (`prop:dense`), pointwise and average | `prop_dense_cost`, `prop_dense` (`Section3/Dense.lean`) | verified |
| Proposition 3.5 (`prop:near-dense`), `m = 2^n - n - 1`, `n ≥ 3` | `prop_near_dense_one` (`Section3/NearDense.lean`) | verified |
| Proposition 3.5, `m = 2^n - n - 2`, `n ≥ 4` | `prop_near_dense_two` (`Section3/NearDense2.lean`) | verified |
| Lemmas 4.1–4.3, Theorem 4.4 and (a)–(c) | `theorem_4_4` (`Section4/Theorem44.lean`); see `Section4/STATUS.md` | verified |

Not formalized: Proposition 3.1; the computations of Section 3 (the engines, the Vandermonde reconstruction of
the `a_j`, Table 1, the exact values for `n ≤ 6`, the enumeration of missing words); the remark on the maximum
length.

## Section 3 modules (dependency order)

| Module | Content |
|---|---|
| `TreeDepth` | total depth `D(S)` of the greedy subtree on a candidate set; `D(S) = |S| + D(S_1) + D(S_0)` |
| `Dense` | `cdepth`, `completeCost`; subcubes with at most `k` missing words; Proposition 3.4 |
| `Missing` | missing words, `|S_b| + r_b = 2^{k-1}`, radius-1 balls, the classification lemma, children |
| `NearBall` | `k + 1` missing words: excess `1` iff the missing words form a ball |
| `Counting` | `𝒜_{n,m} ≃ (Fin m ↪ {0,1}^n)`, `m!` tables per set of columns, `t - C(m)` as a mean of `D - cdepth` |
| `NearDense` | Proposition 3.5, first formula |
| `Optimal` | `cdepth` is the least total depth; balanced forks; `m ≤ 3`; the comb |
| `RowList` | the tree of a row list; invariance under complements and repeated rows |
| `StirlingSum` | `k! S(n,k) = ∑_j (-1)^{k-j} C(k,j) j^n` |
| `FirstsCount` | `∑_τ Φ(firsts τ) = ∑_k S(n,k) ∑_{e : Fin k ↪ T} Φ(e)` |
| `SmallM` | types, `B_k`, `a_j`, `N_m(n)`; Proposition 3.2 and the properties of `B_k`, `J` |
| `Asymptotic` | Corollary 3.3 |
| `NearTwo`, `NearTwoTop`, `NearTwoSets`, `PairCount`, `NearTwoCount`, `NearDense2` | Proposition 3.5, second formula |
| `Check3` | `#check` and `#print axioms` of the final theorems |
| `Mobius` | Proposition 3.1, step: `∑_π μ(π) [x constant on the blocks of π] = [x injective]` over `OrderedFinpartition m` |
| `SmallItems` | Stirling form of Proposition 3.2, `B_k` as a sum over `𝒯_k`, `N_m(n) = 0` for `2^n < m` |
| `NumerZero` | a constant row inserted into a row list leaves the tree unchanged; `B_{k+1} = B'_{k+1} + (k+1)B'_k`; `N_m(0) = 0` |
| `Examples` | `C(2^k) = k` and exact instances of Propositions 3.2, 3.4, 3.5 |
| `PathFork`, `PathShape`, `PathGreedy`, `PathFactor`, `PathMobius`, `PathRows`, `PathDefs`, `PathChainBridge`, `PathEvent`, `PathCells`, `PathCoeff`, `PathCoeff2` | Proposition 3.1, steps: fork counting, path shape, greedy step, Möbius step and row factorization, definitions of the right-hand side; rowwise conditions ⇔ greedy path; cells and Möbius inversion within each cell; `∑_{type λ} μ = c(λ)` |
