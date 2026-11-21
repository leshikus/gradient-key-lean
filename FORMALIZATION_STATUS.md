# Formalization status

Lean `v4.36.0`, Mathlib `v4.36.0`. `lake build` exits with 0. No `sorry`, `admit`, `axiom`, `unsafe` or
`native_decide` in `Section3/*.lean` or `Section4/*.lean`. Every final theorem below depends only on `propext`,
`Classical.choice`, `Quot.sound` (`logs/check3.log`, `logs/theorem_4_4_print.log`).

The model is the article's: `Table n m = Fin n → Fin m → Bool`, `DistinctColumns`, `greedyRow` = the first row of
largest quality `min(k, s-k)`, `leafDepth` = number of forks on the path of a column, `cost = (1/m) ∑_j L_j`,
`tG n m = t_{n,m}(G)` (average over `𝒜_{n,m}`), `completeCost m = C(m) = ℓ + 2 - 2^{ℓ+1}/m`.

| Article | Lean | Status |
|---|---|---|
| Proposition 3.1 (`prop:path-formula`) | — | not formalized |
| Proposition 3.2 (`prop:small-m`): `t - C(m) = N_m(n)/(2^n)_m`, `N_m(n) = ∑_{j=1}^M a_j (2j)^n` | `prop_small_m` (`Section3/SmallM.lean`) | verified |
| — `B_k ≥ 0`, `B_M = 0`, all `B_k = 0` for `m ≤ 3`, `B_{m-1} > 0` for `m ≥ 4`, `M = 2^{m-1}` | `Bint_nonneg`, `Bint_numTypes`, `Bint_small`, `Bint_comb`, `numTypes_eq` | verified |
| — `m - 1 ≤ J < M`, `a_J = B_J/J! > 0` | `J_bounds`, `coeffA_J` | verified |
| Corollary 3.3 (`cor:exp`), with explicit `C`, `N₀` | `cor_exp` (`Section3/Asymptotic.lean`) | verified |
| Result 3, `m ≤ 3`: excess `0` | `excess_small` | verified |
| Proposition 3.4 (`prop:dense`), pointwise and average | `prop_dense_cost`, `prop_dense` (`Section3/Dense.lean`) | verified |
| Proposition 3.5 (`prop:near-dense`), `m = 2^n - n - 1`, `n ≥ 3` | `prop_near_dense_one` (`Section3/NearDense.lean`) | verified |
| Proposition 3.5, `m = 2^n - n - 2`, `n ≥ 4` | `prop_near_dense_two` (`Section3/NearDense2.lean`) | verified |
| Lemmas 4.1–4.3, Theorem 4.4 and (a)–(c) | `theorem_4_4` (`Section4/Theorem44.lean`); see `Section4/STATUS.md` | verified |

Not formalized: Proposition 3.1; the computations of Section 3 (the engines, the Vandermonde reconstruction of
the `a_j`, Table 1, the exact values for `n ≤ 6`, the enumeration of missing words, `N_m(n) = 0` for
`n < ⌈log m⌉` and `N_m(0) = 0`); the remark on the maximum length.

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
