# P9 — Adversarial Lean and mathematical audit of Section 4

## Shared context and non-negotiable rules

Read the attached `article.tex` (Section 4, especially Lemmas 4.1–4.3 and Theorem 4.4), `GradientKeySection4.lean` (version 4, ~1,735 lines), and `GradientKeySection4_STATUS.md` before editing. The article, not an earlier assistant summary, is the source of the mathematical theorem. The Lean file is a **candidate, not compiler-verified**. Preserve the paper's mathematical meaning, including first-in-row-order tie breaking and row-deleted tables with duplicate columns.

**Work in your own named file**; do not overwrite `GradientKeySection4.lean` or another agent's file. Prefer importing the baseline if it compiles. If the baseline is broken, give a minimal isolated module and an integration patch rather than inventing a proof of an unrelated statement. Avoid `sorry`, `admit`, `axiom`, `unsafe`, and unnecessary new hypothesis parameters. Existing hypotheses may appear in a *stated interface* only if you clearly identify which agent must discharge them; they do not count as completion. Test using a pinned Lean 4 + Mathlib project (`lake env lean YourFile.lean`) whenever possible, providing exact command, toolchain revision, and output. If unavailable, say **NOT COMPILED** and do not claim verification. Never hide a compiler failure or silently weaken the target proposition.

Return: (1) standalone Lean source or a precise patch, (2) theorem declarations and their status, (3) dependencies on other agents, (4) actual compilation results/errors, and (5) a minimal merge plan. Minimize changes to unrelated sections.

## Your assignment

You are the independent **skeptical reviewer**, not an implementation agent. Try to falsify the mathematics and the Lean model before spending effort proving it. Do not accept 'no sorry' as evidence that code compiles.

Audit against the paper's exact definitions:
1. Does `Concrete.greedyRow` choose the **first** maximum-quality row, including ties? Verify the Mathlib/List API and run small tests if possible.
2. Does allowing all rows as candidates falsely permit reuse? Is the selected row indeed constant on every descendant candidate set, and is there always another splitting row at a non-singleton candidate set?
3. Could a deleted-row tree terminate with a non-singleton candidate set? Does `PairClosed` still hold? Does prefix coupling fail if row index order changes?
4. Is `Extension B` nonempty precisely when the conditional event has positive probability? Is conditional uniformity valid when the chosen column `j` is fixed?
5. Check every real/natural coercion and division by `S.card`, `n-i`, `Fintype.card`. Pay special attention to the `S=∅`, `n=0`, `m=2` and `n=ell` edge cases.
6. Can the existing v4 `conditional_inserted_imbalance_exact` fail due to a Lean tactic/API issue or a mathematical sign error? Verify it with the supplied `verify_row_deletion.py` or independent exhaustive enumeration.
7. Check the exact equivalence between expected path depth and the paper's `t_{n,m}(G)`; verify no hidden change to sampling weights.
8. Search for unproved assumptions, shadowed names, inaccessible `private` declarations, and silent weakening of the theorem statement.

Deliver `P9_Audit.md`: rank findings as mathematical error, model mismatch, compilation blocker, or stylistic issue; provide smallest counterexample or exact failing Lean command when possible; suggest **local** corrections. Do not rewrite the entire proof or treat a concern as proven falsehood without evidence.
