# P3 — Row deletion/insertion bijection and conditional law

## Shared context and non-negotiable rules

Read the attached `article.tex` (Section 4, especially Lemmas 4.1–4.3 and Theorem 4.4), `GradientKeySection4.lean` (version 4, ~1,735 lines), and `GradientKeySection4_STATUS.md` before editing. The article, not an earlier assistant summary, is the source of the mathematical theorem. The Lean file is a **candidate, not compiler-verified**. Preserve the paper's mathematical meaning, including first-in-row-order tie breaking and row-deleted tables with duplicate columns.

**Work in your own named file**; do not overwrite `GradientKeySection4.lean` or another agent's file. Prefer importing the baseline if it compiles. If the baseline is broken, give a minimal isolated module and an integration patch rather than inventing a proof of an unrelated statement. Avoid `sorry`, `admit`, `axiom`, `unsafe`, and unnecessary new hypothesis parameters. Existing hypotheses may appear in a *stated interface* only if you clearly identify which agent must discharge them; they do not count as completion. Test using a pinned Lean 4 + Mathlib project (`lake env lean YourFile.lean`) whenever possible, providing exact command, toolchain revision, and output. If unavailable, say **NOT COMPILED** and do not claim verification. Never hide a compiler failure or silently weaken the target proposition.

Return: (1) standalone Lean source or a precise patch, (2) theorem declarations and their status, (3) dependencies on other agents, (4) actual compilation results/errors, and (5) a minimal merge plan. Minimize changes to unrelated sections.

## Your assignment

You own the **probabilistic conditioning bridge** for Lemma 4.2, not the Hoeffding inequality. Use `GradientKey.RowDeletion.RemainingTable`, `SameColumn`, `ValidExtension`, `Extension`, and `conditional_inserted_imbalance_exact`; cross-check `GradientKey.Concrete.Sample`.

Goals:
1. Define `deleteRow : Table n m → Fin n → RemainingTable (n-1) m` (or a robust `Fin.succAbove` equivalent), and a converse `insertRow`, preserving the order of undeleted rows and respecting the insertion index.
2. Prove `insertRow` and `deleteRow` give a bijection between valid full tables with fixed deleted table `B` and `Extension B`; prove feasibility/nonemptiness exactly when this fibre is nonempty.
3. Include the independent uniform choice of `j : Fin m`. Prove that conditioning on `deleteRow A r=B` and `j=j₀` makes inserted row **uniform** over `Extension B`. Do this as an exact ratio of finite sums / cardinalities if conditional-probability infrastructure is cumbersome.
4. Prove finite 'tower' / fibre averaging statements transferring conditional expectation ≤1 to the unconditional expectation `E[U_r]≤1`. Supply the analogous transfer for `Pr(U_r>z)` from a fibrewise tail bound, without assuming independence of candidate sets and inserted rows.
5. Expose an accessible finite-average API if the baseline declares it `private`; coordinate export with P0 rather than copying hidden assumptions.

Deliver `P3_ConditionalFibre.lean` with a reusable generic finite fibre-disintegration lemma and specialized row-deletion corollaries. State all cardinality/positive-probability guards explicitly; avoid division by zero.
