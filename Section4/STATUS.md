# Section 4 in Lean: status

Lean `v4.36.0`, Mathlib `v4.36.0` (commit pinned in `lake-manifest.json`).
`lake build Section4` and `lake env lean Section4/Check.lean` exit with 0.
No `sorry`, `admit`, `axiom`, `unsafe` or `native_decide` in `Section4/*.lean`.
`#print axioms theorem_4_4`: `propext`, `Classical.choice`, `Quot.sound`.

## Verification matrix

| Result | Lean declaration | Compiles | Hypotheses beyond the article's |
|---|---|---|---|
| Greedy invariants (nesting, split, no reuse, end by depth `n`, path tail) | `P1_GreedyPath`: `p1_no_row_reuse`, `p1_terminates_by_n`, `p1_sample_hTail`, `p1_finitePathData` | yes | none |
| Lemma 4.1 (recurrence) | `Lemma41.concrete_expectedExcess_succ` | yes | none |
| Lemma 4.1 (tail `t ≤ ∑ p_i + E(s_h-1)`) | `FinitePathData.expectedTail` with `p1_finitePathData` | yes | none |
| Lemma 4.2, mean | `RowDeletion.conditional_inserted_imbalance_exact`, `_le_one` | yes | none |
| Lemma 4.2, tail | `Hoeffding.conditional_inserted_imbalance_tail` | yes | none |
| Conditioning on `∂_r A = B`, `j = j₀` | `P3_ConditionalFibre.sampleFibreEquiv`, `unconditional_row_mean_le_one`, `unconditional_row_tail_of_extension_tails` | yes | none |
| Deleted path, pair closure, prefix coupling | `DeletedPath.delCand_congr`, `delCand_pairClosed`, `delCand_eq_candidateAt` | yes | none |
| Lemma 4.3, first bound | `Lemma43.expectedImbalance_le_rows` | yes | none |
| Lemma 4.3, logarithmic bound | `Lemma43.expectedImbalance_le_log` (truncation: `Truncation.sum_on_event_le_phi`) | yes | none |
| Theorem 4.4, displayed bound and (a)–(c) | `GradientKeySection4.theorem_4_4_from_finite_paths` | yes | the Lemma 4.1/4.3 estimates, discharged below |
| `E[sampleDepth] = t_{n,m}(G)` | `Theorem44.expectedDepth_eq_tG`, `leafDepth_eq_pathDepth` | yes | none |
| Sample space nonempty | `Theorem44.sample_nonempty` | yes | none |
| Final theorem | `Theorem44.theorem_4_4` | yes | only `2 ≤ m`, `m ≤ 2^n`, and `2ℓ - 2 ≤ n` in (c) |

## What was done to each draft

| Draft | Use |
|---|---|
| Baseline v4 | 11 compiler errors fixed in place (including the P9 `partner_twice` orientation; the same reversal also occurred in `duplicate_sign_sum_zero`); `finiteAverage` API made public; `Fintype (ValidTable n m)` instance added |
| P1 | compiler errors fixed; used as is |
| P2 | errors fixed; `fiber` takes `[DecidableEq C]`; connected to `candidateAt` in `Lemma41.lean` |
| P3 | errors fixed; duplicate `Fintype` instance removed; used as is |
| P4 | not used: it models the full path with its own available-row state, not the baseline `candidateAt`. `DeletedPath.lean` defines `G(∂_r A)` directly with the baseline's `greedyRow` rule and proves the coupling against `candidateAt`. The original is kept in `drafts/original/`. |
| P5 | errors fixed; its exact mgf (`unique_sign_mgf_exact`) feeds the Chernoff bound in `Hoeffding.lean` |
| P6 | not used: its interface hypotheses are proved directly in `Lemma43.lean`. The original is kept in `drafts/original/`. |
| P7 | errors fixed; `htrunc` proved in `Truncation.lean` (layer cake for the counting measure, split at `z = 2 ln(2/q)`) |
| P8 | compiles unchanged; it is not on the dependency path of `theorem_4_4` |
| P9 | patch applied; its Python check passes |

The Python regression scripts (`drafts/original/*.py`) all pass; their output is in `logs/python/`.
