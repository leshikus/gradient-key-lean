# P1 greedy-path proof candidate — integration and verification report

## Source and provenance

- Mathematical source: `article(2).tex`, Section 4, particularly the paragraph defining `S_i` and Lemma 4.1.
- Baseline: recovered version-4 text `GradientKeySection4.lean` from the project Library; it is the **uncompiled candidate**, not a trusted binary dependency.
- Baseline status: `GradientKeySection4_STATUS.md` v4 says `UNCHECKED` and lists the greedy-path obligation as open.
- New source: `P1_GreedyPath.lean`, importing the unmodified baseline and declaring its theorems in `GradientKey.Concrete`.
- Integration alternative: `P1_GreedyPath_integration.patch`, which inserts the helper declarations only in `Concrete` and changes `Concrete.finitePathData` to take only `hn`.

## Lean declaration coverage (all NOT COMPILED)

| Assigned obligation | Candidate declarations |
|---|---|
| Membership / nesting / nonemptiness | `p1_step_subset`, `p1_step_mem`, `p1_candidate_mem`, `p1_candidate_subset_succ`, `p1_candidate_subset_of_le`, `p1_candidate_nonempty`, `p1_candidate_stays_singleton` |
| Existence of splitting row / greedy optimality | `p1_quality_pos_of_diff`, `p1_exists_positive_row`, `p1_greedy_quality_max`, `p1_greedy_quality_pos`, `p1_greedy_step_card_lt` |
| First-row tie breaking | `p1_argmax_some`, `p1_greedy_first_max` (Mathlib `List.index_of_argmax`, `List.idxOf_finRange`) |
| Row constant after use / no row reuse | `p1_step_selected_constant`, `p1_selected_inactive_after_step`, `p1_no_row_reuse` |
| Strict decrease / termination | `p1_path_card_step`, `p1_activeRows_card_lt_at_fork`, `p1_activeRows_budget`, `p1_terminates_by_n`, `p1_terminated_after_n` |
| Complete path depth | `p1_depth_eq_forks`, `p1_no_forks_after_n`, `p1_forks_stabilize`, `p1_depth_equals_complete_path` |
| Pointwise tail for any h | `p1_candidate_budget_anti`, `p1_path_tail_nat`, `p1_sample_hTail` |
| Public `FinitePathData` without assumed hTail | `p1_finitePathData`; direct integration patch instead updates original `finitePathData` |

The assertions use no new mathematical assumptions beyond the original `DistinctColumns` and `0 < n` parameters. No `sorry`, `admit`, `axiom`, or `unsafe` is used. This is **not** a statement of kernel verification.

## Main argument

Let `activeRows(A,S,j)` be the set of original rows on which some column of `S` differs from column `j`. If `S` is a non-singleton with distinct columns, it admits a positive-quality row. By `List.argmax` maximality, the chosen row also has positive quality, so `candidateStep` strictly decreases `S` and the chosen row becomes inactive. Inactive rows remain inactive because candidates are nested. Therefore each fork strictly reduces the active-row count, which starts at most `n`; by depth `n` the candidate set is `{j}`.

Let `fork(i)` be 1 when `|S_i| >= 2` and 0 otherwise. The stronger pointwise inequality `fork(i) + |S_{i+1}| <= |S_i|` telescopes. Since all candidate sets are nonempty, for `h<=n` this bounds the remaining actual forks by `|S_h|-1`; for `h>n` the prefix already includes all the first `n` forks and the extra `|S_h|-1` is nonnegative. This establishes the exact displayed `hTail`, with no probability theory.

## Actual testing performed

- `command -v lean`: no executable found.
- `command -v lake`: no executable found.
- `curl -I https://github.com/leanprover/lean4/releases/latest`: failed with DNS resolution error.
- `lake env lean P1_GreedyPath.lean`: **NOT RUN**, because `lake` and the Mathlib project do not exist here.
- Toolchain version/revision: **unavailable; not pinned**.
- `python P1_check.py`: **PASS** over 4,054 distinct-column tables, all columns of each table, including `n=1`, `m=2`, `m=2^n`, and cutoffs `h>n` (through `n+5`). This verifies the mathematics in an independent Python model, **not the Lean proof**.
- `patch --dry-run -p1 < P1_GreedyPath_integration.patch` against the reconstructed v4 source: **PASS**.

## Dependencies on other agents

- **P0** must establish a compiling, pinned Mathlib baseline. The new source imports it and cannot be checked independently until P0 resolves any baseline elaboration/API errors.
- **P10** (integration) should import `P1_GreedyPath` and use `Concrete.p1_finitePathData hn`, or apply the provided integration patch to a clean v4 baseline and retain the original public name `Concrete.finitePathData hn`.
- No dependency on row deletion, probability, or conditional moment estimates; those are separate agent assignments.

## Minimal merge plan

Option A (leave baseline unchanged): ensure `GradientKeySection4.olean` compiles, then `import P1_GreedyPath`; replace downstream calls of `Concrete.finitePathData hn hTail` by `Concrete.p1_finitePathData hn`.

Option B (single-file merge): apply `P1_GreedyPath_integration.patch` to `GradientKeySection4.lean`. It only adds declarations in `Concrete` and changes the original `finitePathData` signature/`pathTail` field. **Do not additionally import the standalone P1 module after this patch**, since it declares the same names.

After either merge, run `lake env lean ...` with P0's pinned toolchain and address compiler diagnostics. Do not claim the Lean proof is complete until all declarations elaborate and the kernel accepts them.
