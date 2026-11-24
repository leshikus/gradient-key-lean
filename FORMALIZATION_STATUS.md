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
| Lemma 3.1 (`lem:distinct`): the number of matrices with distinct columns and row `i` in `R_i` is `∑_p μ(p) ∏_i r_i(p)` | `card_valid_with_row_constraints` (`Section3/PathMobius.lean`); set partitions as Mathlib's `OrderedFinpartition` (blocks ordered by least element), `R_i` given by a predicate `P i` | verified |
| Proposition 3.2 (`prop:path-formula`): `t_{n,m}(G) = (2^n)_m⁻¹ ∑_s ∏_{j<d} C(s_j-1,s_{j+1}-1) ∑_ρ ∑_p μ(p) ∏_i r_i^ρ(p)`, for any fixed candidate sets per chain | `prop_path_formula_sets` (`Section3/PathFormula.lean`), from `card_path_eq` (`PathEvent`, one family of candidate sets) | verified |
| — the grouped form, equation (1): `t_{n,m}(G) = (2^n)_m⁻¹ ∑_s ∏_{j<d} C(s_j-1,s_{j+1}-1) ∑_λ ∏_j c(λ_j) F_n` | `prop_path_formula` (`tG n m hn = pathFormulaRHS n m`, `0 < n`, `2 ≤ m`); per-chain identity `chain_count` (the summand of a chain is the number of valid tables in which column `j₀` has candidate sets of the chain's sizes) | verified |
| — each chain term is a nonnegative integer; a chain of depth `0` contributes `(2^n)_m` | `chain_term_natural`, `chain_term_nonneg`, `path_chain_term_depth_zero` (`Section3/PathFormula.lean`), from `chain_count` | verified |
| — pruning: a chain contributes `0` if `q_j(n-j) < s_j - 1` or `max(Δ_j, s_{j+1}) > 2^{n-j-1}` for some `j < d` | `prop_path_prune`, from `path_shape_bounds` (the inequalities hold for every path that occurs) (`Section3/PathPrune.lean`) | verified |
| — the example `(n,m) = (3,4)` on the definitions: the chains are `(4)`, `(4,2)`, `(4,3)`, `(4,3,2)`; chain terms `1680`, `1488`, `144`, `96` (`c(λ)` and `F_3` for each type; for `(4,2)`: `(W(∅),W({0})) = (10,16), (6,8), (6,8), (2,4)`, `V_0 = 2`, `F_3 = 1032, 296, 296, 56`); `(2^3)_4⁻¹ · 3408 = 3408/1680`, equal to `example_n3_m4` | `example34_chains`, `example34_chain4`, `example34_chain42`, `example34_chain43`, `example34_chain432`, `example34_coeff`, `example34_W`, `example34_V`, `example34_F`, `example34_F43`, `example34_F432`, `example34_rhs`, `example34_tG`, `path_formula_n3_m4_total` (`Section3/PathExample.lean`) | verified |
| Section 3.1, recurrence for `F_n`: `D_i(M)` = sum over injective `ρ : M → {1,…,i}` of `∏_{i'∉im ρ} W(M_{i'}) ∏_{j∈M} V_j(M_{ρ(j)})`, `M_{i'} = {j ∈ M : ρ(j) < i'}`; `D_0(∅)=1`, `D_0(M)=0` for `M≠∅`, `D_{i+1}(M) = D_i(M)W(M) + ∑_{j∈M} D_i(M∖{j})V_j(M∖{j})`; `F_n = D_n({0,…,d-1})` | `pathD` (the recurrence, as a definition), `pathD_eq_sum` (the sum over `M ↪ Fin i`, any `i`, `M`), `pathF_eq_pathD`; `pathD_empty` (`D_i(∅) = W(∅)^i`), `pathD_eq_zero_of_lt_card` (`|M| > i`); example `(4,2)`: `example34_D` (`D_3 = 1032, 296, 296, 56` from `W`, `V_0`), `example34_F_eq_D` (`Section3/PathRecurrence.lean`). Not the C++ engine | verified |
| Proposition 3.3 (`prop:small-m`): `t - C(m) = N_m(n)/(2^n)_m`, `N_m(n) = ∑_{j=1}^M a_j (2j)^n` | `prop_small_m` (`Section3/SmallM.lean`) | verified |
| — `B_k ≥ 0`, `B_M = 0`, all `B_k = 0` for `m ≤ 3`, `B_{m-1} > 0` for `m ≥ 4`, `M = 2^{m-1}` | `Bint_nonneg`, `Bint_numTypes`, `Bint_small`, `Bint_comb`, `numTypes_eq` | verified |
| — `m - 1 ≤ J < M`, `a_J = B_J/J! > 0` | `J_bounds`, `coeffA_J` | verified |
| — `N_m(n) = 2^n ∑_k B_k S(n,k)`; `k! S(n,k) = ∑_j (-1)^{k-j} C(k,j) j^n` | `prop32_stirling_form`, `prop32_stirling_identity` (`Section3/SmallItems.lean`) | verified |
| — `B_k = ∑_{T ∈ 𝒯_k} (L̄(G(T)) - C(m))` (`T : Fin k ↪ Ty`, `G(T)` on `tblOf T`), `k ≥ 1` | `Bk_eq_tuple_sum` | verified |
| — the `B_k` are integers: column symmetry `∑_{T∈𝒯_k} ∑_j L_j = m ∑_{T∈𝒯_k} L_1`; `m! ∣ 2^k |𝒯_k|` (free action of column permutations on the representative tables); `m ∣ m B_k` for every `k` | `sum_ldepth_eq`, `factorial_dvd_card`, `Bint_dvd`, `Bk_integer` (`Section3/BkInteger.lean`; hypothesis `0 < m` only) | verified |
| Computation paragraph: `N_m(n) = 0` for `n ≥ 1`, `2^n < m` | `numer_eq_zero_of_two_pow_lt` | verified |
| Computation paragraph: `N_m(0) = 0`, via `∑_k (-1)^k B_k/k! = 0` (constant row type inserted) | `numer_zero`, `alt_sum_Bint` (`Section3/NumerZero.lean`) | verified |
| Examples: `t_{n,2^n} = n`, `t_{1,2} = 1`, `t_{n,2} = 1`, `t_{3,4} = 3408/1680`, `t_{4,11} - C(11) = 1/3003`, `t_{4,10} - C(10) = 18/5005` | `example_full`, `example_n1_m2`, `example_m2`, `example_n3_m4`, `example_n4_m11`, `example_n4_m10` (`Section3/Examples.lean`) | verified |
| Corollary 3.4 (`cor:exp`), with explicit `C`, `N₀` | `cor_exp` (`Section3/Asymptotic.lean`) | verified |
| Result 3, `m ≤ 3`: excess `0` | `excess_small` | verified |
| Proposition 3.5 (`prop:dense`), pointwise and average | `prop_dense_cost`, `prop_dense` (`Section3/Dense.lean`) | verified |
| Proposition 3.6 (`prop:near-dense`), `m = 2^n - n - 1`, `n ≥ 3` | `prop_near_dense_one` (`Section3/NearDense.lean`) | verified |
| Proposition 3.6, `m = 2^n - n - 2`, `n ≥ 4` | `prop_near_dense_two` (`Section3/NearDense2.lean`) | verified |
| Lemmas 4.1–4.3, Theorem 4.4 and (a)–(c) | `theorem_4_4` (`Section4/Theorem44.lean`); see `Section4/STATUS.md` | verified |

Not formalized: the computations of Section 3 (the engines, the Vandermonde reconstruction of
the `a_j`, Table 1, the exact values for `n ≤ 6`, the enumeration of missing words); the remark on the maximum
length.

## Section 3 modules (dependency order)

| Module | Content |
|---|---|
| `TreeDepth` | total depth `D(S)` of the greedy subtree on a candidate set; `D(S) = |S| + D(S_1) + D(S_0)` |
| `Dense` | `cdepth`, `completeCost`; subcubes with at most `k` missing words; Proposition 3.5 |
| `Missing` | missing words, `|S_b| + r_b = 2^{k-1}`, radius-1 balls, the classification lemma, children |
| `NearBall` | `k + 1` missing words: excess `1` iff the missing words form a ball |
| `Counting` | `𝒜_{n,m} ≃ (Fin m ↪ {0,1}^n)`, `m!` tables per set of columns, `t - C(m)` as a mean of `D - cdepth` |
| `NearDense` | Proposition 3.6, first formula |
| `Optimal` | `cdepth` is the least total depth; balanced forks; `m ≤ 3`; the comb |
| `RowList` | the tree of a row list; invariance under complements and repeated rows |
| `StirlingSum` | `k! S(n,k) = ∑_j (-1)^{k-j} C(k,j) j^n` |
| `FirstsCount` | `∑_τ Φ(firsts τ) = ∑_k S(n,k) ∑_{e : Fin k ↪ T} Φ(e)` |
| `SmallM` | types, `B_k`, `a_j`, `N_m(n)`; Proposition 3.3 and the properties of `B_k`, `J` |
| `Asymptotic` | Corollary 3.4 |
| `NearTwo`, `NearTwoTop`, `NearTwoSets`, `PairCount`, `NearTwoCount`, `NearDense2` | Proposition 3.6, second formula |
| `Check3` | `#check` and `#print axioms` of the final theorems |
| `Mobius` | Lemma 3.1, step: `∑_p μ(p) [x constant on the blocks of p] = [x injective]` over `OrderedFinpartition m` |
| `SmallItems` | Stirling form of Proposition 3.3, `B_k` as a sum over `𝒯_k`, `N_m(n) = 0` for `2^n < m` |
| `NumerZero` | a constant row inserted into a row list leaves the tree unchanged; `B_{k+1} = B'_{k+1} + (k+1)B'_k`; `N_m(0) = 0` |
| `Examples` | `C(2^k) = k` and exact instances of Propositions 3.3, 3.5, 3.6 |
| `PathFork` | fork counting: `tG_eq_forkTableCounts` |
| `PathShape` | shape of candidate-set chains: `pathFork_depth_lt_n`, `pathFork_size_budget` |
| `PathGreedy` | one greedy step: `pathOneStepTest_iff` |
| `PathFactor` | Möbius step and row factorization: `card_row_constraints_constOn` |
| `PathMobius` | Lemma 3.1: `card_valid_with_row_constraints` |
| `PathRows` | path conditions on rows for fixed candidate sets: `fixedPath_mobius_factor` |
| `PathDefs` | definitions of the right-hand side: chains, `c(λ)`, `W`, `V_j`, `F_n` |
| `PathChainBridge` | every fork gives a chain: `pathChainOfFork_sizes` |
| `PathEvent` | path conditions ⇔ greedy path; count for one family of candidate sets: `card_path_eq` |
| `PathCells` | Möbius inversion within cells: `card_path_cells` |
| `PathCoeff`, `PathCoeff2` | `∑_{type λ} μ = c(λ)`: `sum_mu_by_type` |
| `PathBlocks` | rows constant on blocks: `card_rows_eq_blk` |
| `PathRowCount` | row counts depend only on block sizes: `rowcount_eq_cntU` |
| `PathGroup` | grouping by types: `sum_mu_pi` |
| `PathWV` | row counts are `W` and `V_j`: `cntU_W`, `cntU_V` |
| `PathFixed` | count for one family of candidate sets, grouped: `card_path_fixed` |
| `PathFamily` | number of families: `card_pathFams` |
| `PathFormula` | Proposition 3.2 and equation (1): `prop_path_formula_sets`, `prop_path_formula`, `chain_count`; `chain_term_natural`, `path_chain_term_depth_zero` |
| `PathPrune` | pruning: `prop_path_prune`, `path_shape_bounds` |
| `PathExample` | the example `(3,4)`: `example34_chains`, `example34_chain4/42/43/432`, `example34_rhs`, `example34_tG` |
| `PathRecurrence` | the row-by-row recurrence for `F_n`: `pathD`, `pathD_eq_sum`, `pathF_eq_pathD`, `example34_D` |
| `BkInteger` | the `B_k` are integers: `sum_ldepth_eq`, `factorial_dvd_card`, `Bint_dvd`, `Bk_integer` |
