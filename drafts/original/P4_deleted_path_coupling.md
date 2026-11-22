# P4 — Greedy paths after deleting a row, pair closure and coupling

## Shared context and non-negotiable rules

Read the attached `article.tex` (Section 4, especially Lemmas 4.1–4.3 and Theorem 4.4), `GradientKeySection4.lean` (version 4, ~1,735 lines), and `GradientKeySection4_STATUS.md` before editing. The article, not an earlier assistant summary, is the source of the mathematical theorem. The Lean file is a **candidate, not compiler-verified**. Preserve the paper's mathematical meaning, including first-in-row-order tie breaking and row-deleted tables with duplicate columns.

**Work in your own named file**; do not overwrite `GradientKeySection4.lean` or another agent's file. Prefer importing the baseline if it compiles. If the baseline is broken, give a minimal isolated module and an integration patch rather than inventing a proof of an unrelated statement. Avoid `sorry`, `admit`, `axiom`, `unsafe`, and unnecessary new hypothesis parameters. Existing hypotheses may appear in a *stated interface* only if you clearly identify which agent must discharge them; they do not count as completion. Test using a pinned Lean 4 + Mathlib project (`lake env lean YourFile.lean`) whenever possible, providing exact command, toolchain revision, and output. If unavailable, say **NOT COMPILED** and do not claim verification. Never hide a compiler failure or silently weaken the target proposition.

Return: (1) standalone Lean source or a precise patch, (2) theorem declarations and their status, (3) dependencies on other agents, (4) actual compilation results/errors, and (5) a minimal merge plan. Minimize changes to unrelated sections.

## Your assignment

You own the **row-deleted greedy algorithm and path agreement** used in Lemma 4.3. The current `Concrete` path assumes a valid full table; the paper explicitly allows repeated columns after deleting a row. Implement that separate case correctly.

Tasks:
1. Define a greedy path on an arbitrary binary table `B : RemainingTable ...` whose columns may repeat: at a node, test the first maximum-quality row if a splitting row exists; otherwise stop and retain a terminal candidate set that may have size >1. After termination the candidate set remains unchanged at all later depths.
2. Define `deletedCandidate A r j i` as `S_i^{(-r)}` and `U_r = v_r(S_i^{(-r)})` with correct handling of always-nonempty candidate sets.
3. Show every `S_i^{(-r)}` is `RowDeletion.PairClosed (deleteRow A r) (S_i^{(-r)})`: two equal columns in the reduced matrix cannot be separated by any reduced row.
4. Prove *prefix coupling*: on event `E_r` that the full valid greedy path has a fork at depth `i` and row `r` was not tested at depths `<i`, the reduced path matches the full path at every depth `≤i`. Preserve the first-by-original-row-order tie-breaking after deletion.
5. Establish that on `E_r` the full path's `v_r(S_i)` equals `U_r`, and exactly `n-i` rows are unused on any full path with `s_i≥2`.
6. Supply the pointwise greedy comparison `v_i 1_{s_i≥2} ≤ (1/(n-i)) ∑_r 1_{E_r} U_r` for `i<n`.

Deliver `P4_DeletedPath.lean` with explicit lemmas suitable for P6/P7. Do not assume deleted columns remain distinct.
