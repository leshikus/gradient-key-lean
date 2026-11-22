# Proposition 3.1 — Lean proof development, 2026-11-22

Repository: https://github.com/leshikus/gradient-key-lean
Target: **main** (the only branch; PR #1 merged). Pinned Lean/Mathlib **v4.36.0**.

## Verification statement

**All eight Lean modules compile** with the pinned Lean/Mathlib `v4.36.0`
(`lake build PathFork PathShape PathGreedy PathFactor PathMobius PathRows PathDefs PathChainBridge`,
exit 0, 2026-11-22). No `sorry`, `admit`, `axiom`, `native_decide` or `unsafe`.
`#print axioms` gives `[propext, Classical.choice, Quot.sound]` for `tG_eq_forkTableCounts`,
`pathCandidates_step_ssubset`, `pathFork_size_budget`, `pathOneStepTest_iff`, `mobius_table_indicator`,
`card_valid_with_row_constraints`, `fixedPath_card_factor`, `fixedPath_mobius_factor`, `pathChainOfFork_sizes`.
Pushed in `1b6ef89` (PR #1, merged into `main` as `5c13cb1`); CI passed.

Fixes needed to compile the original drafts:

- `PathFork`: `div_div_eq_div_mul` (not in this Mathlib) replaced by `div_div`; `congrArg (fun x => x / …)`
  replaced by `congr 1`.
- `PathFactor`, `PathMobius`, `PathRows`, `PathDefs`, `PathChainBridge`: `open Classical` (missing
  `Decidable`/`DecidablePred` instances).
- `PathFactor`: `if_congr` for `ite` with different `Decidable` instances (`mobius_table_indicator`);
  `convert` in `card_row_constraints_constOn`.
- `PathMobius`: the `simpa` in `hpoint` left `(∀ i, True) ∧ …`; replaced by `if_congr` and
  `← mobius_table_indicator`.
- `PathRows`: `unfold fixedPathRowwise` before `convert` in both theorems.

Review notes:

- `tG_eq_forkTableCounts` does not use its hypothesis `2 ≤ m`; it can be dropped.
- `PathDefs` is inside `noncomputable section` with `open Classical`, so `decide` cannot evaluate `pathW`,
  `pathV`, `pathF` for the (3,4) checks. Make these definitions computable (decidable filters, no `Classical`)
  before writing those checks.
- `PathDefs` imports `PathMobius` but uses nothing from it.
- `fixedPathRowAdmissible` matches the article: at `i = ρ(j)` the split `S_{j+1} = {k ∈ S_j | row k = row j₀}`;
  at other depths `< q_j` if `i < ρ(j)`, else `≤ q_j`.

The Python tests (`path_formula_certificate.py`, `path_formula_crosscheck.py`,
`path_formula_regression.py`) were reported as passing by their author; they were not re-run here.

## New modules (all drafts)

| File | Intended theorem / component |
|---|---|
| `PathFork.lean` | `tG_eq_forkTableCounts`, connection from `tG` to the sum of valid-table fork counts |
| `PathShape.lean` | `pathCandidates_step_ssubset`, `pathFork_depth_lt_n`, `pathFork_size_budget` |
| `PathGreedy.lean` | `pathOneStepTest_iff`, exact greedy-step row test with tie breaking |
| `PathFactor.lean` | `card_row_constraints_filter`, `mobius_table_indicator`, independent row products |
| `PathMobius.lean` | `card_valid_with_row_constraints`: generic Möbius correction and product across rows |
| `PathRows.lean` | `fixedPathRowAdmissible`, `fixedPath_card_factor`, `fixedPath_mobius_factor` |
| `PathChainBridge.lean` | `pathChainOfFork`: extract the actual decreasing-size chain from each fork |
| `PathDefs.lean` | Exact finite definitions of chains, integer partition multiplicities, `c`, assignments, `W`, `V`, `F_n`, and `pathFormulaRHS` |

## Dependency order

```text
Counting ─ PathFork ─ PathShape ─ PathGreedy ─┐
                                             ├─ PathRows
Counting + Mobius ─ PathFactor ─ PathMobius ─┘
                                      └─ PathDefs ─ PathChainBridge
PathShape ──────────────────────────────────┘
```

Place the Lean files in `Section3/`. Add each file's stem as a root to
`Section3.roots` in `lakefile.toml` **after** fixing all compile errors.
Do not alter the pinned dependencies or add `sorry`, `axiom`, `native_decide`,
or any proof bypasses.

## Open mathematical obligations

1. **Done:** the drafts compile (see above). Register them as Lake roots, add their final theorems to
   `Section3/Check3.lean` and `ci/expected_theorems.txt`, and push. **Done** in `1b6ef89`.
2. **Connect partitions to blocks.** Prove that a `PathPartition m a`
   multiplicity vector represents an ordinary integer partition of `a`
   (for `a≤m`); prove the per-cell Möbius coefficient identity in `ℚ`.
3. **Telescoping cell sizes.** For `S_0 ⊃ ... ⊃ S_d`, show that the union
   of cells indexed `i..d` has size `s_i`. Transfer this to the weighted
   assignment model, so `pathRowQuality` agrees with `rq`.
4. **Greedy path characterization.** For each fixed strictly nested
   family `S` containing column `j₀` and injective schedule `ρ`, prove
   that `fixedPathRowwise S j₀ ρ A` is equivalent to the actual greedy
   path plus selected rows. Prove the choice of `ρ` is unique for any
   actual fork. Use the local `pathOneStepTest_iff` proof and the
   exact selected-row quality `q_j`.
5. **Cell-crossing partitions vanish.** If a partition block meets two
   different cells, show the separating row's admissible count is zero.
6. **Row counts by partition type.** For partitions supported inside
   the individual cells, prove the counts are exactly `pathW` and
   `pathV`; show their product is `pathF` when summed over injections.
7. **Count nested set families.** Prove that the number of nested
   families of sizes `s` containing a fixed `j₀` equals
   `∏_{j<d} choose(s_j-1, s_(j+1)-1)`.
8. **Per-chain identity.** Combine 2–7 to connect each chain's
   `pathChainTerm` to the actual fork count. Then combine with
   `tG_eq_forkTableCounts` and column symmetry to prove
   `prop_path_formula : tG n m hn = pathFormulaRHS n m`.
9. **Both pruning inequalities.** Prove from distinctness and the
   previously used rows that `s_j-1 ≤ (n-j) q_j`, and using the
   untested rows that `max(a_j,s_(j+1)) ≤ 2^(n-j-1)`.
   Derive zero contribution of violating chains **from** the per-chain
   identity, rather than filtering them out of the RHS.

## Required verification before any push

```bash
lake build
lake env lean Section3/Check3.lean
lake env lean Section4/Check.lean
python3 ci/check_proofs.py logs/check3.log logs/check.log
```

For each newly verified final theorem, add `#check` and `#print axioms`
to `Section3/Check3.lean`, add its name to `ci/expected_theorems.txt`,
update `FORMALIZATION_STATUS.md`, and regenerate `logs/check3.log`.
Commit and push every verified update to `main`, and check CI. No other branches or PRs.
