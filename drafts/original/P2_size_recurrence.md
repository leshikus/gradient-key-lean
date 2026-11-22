# P2 — Full finite proof of Lemma 4.1 transition

## Shared context and non-negotiable rules

Read the attached `article.tex` (Section 4, especially Lemmas 4.1–4.3 and Theorem 4.4), `GradientKeySection4.lean` (version 4, ~1,735 lines), and `GradientKeySection4_STATUS.md` before editing. The article, not an earlier assistant summary, is the source of the mathematical theorem. The Lean file is a **candidate, not compiler-verified**. Preserve the paper's mathematical meaning, including first-in-row-order tie breaking and row-deleted tables with duplicate columns.

**Work in your own named file**; do not overwrite `GradientKeySection4.lean` or another agent's file. Prefer importing the baseline if it compiles. If the baseline is broken, give a minimal isolated module and an integration patch rather than inventing a proof of an unrelated statement. Avoid `sorry`, `admit`, `axiom`, `unsafe`, and unnecessary new hypothesis parameters. Existing hypotheses may appear in a *stated interface* only if you clearly identify which agent must discharge them; they do not count as completion. Test using a pinned Lean 4 + Mathlib project (`lake env lean YourFile.lean`) whenever possible, providing exact command, toolchain revision, and output. If unavailable, say **NOT COMPILED** and do not claim verification. Never hide a compiler failure or silently weaken the target proposition.

Return: (1) standalone Lean source or a precise patch, (2) theorem declarations and their status, (3) dependencies on other agents, (4) actual compilation results/errors, and (5) a minimal merge plan. Minimize changes to unrelated sections.

## Your assignment

You own **the expected candidate-size recurrence**. Work independently of the row-deletion estimates, preferably with an abstract finite tree/path interface or an isolated version of `Concrete.Sample`. The mathematical goal is precisely Lemma 4.1:

For every `i ≥ 0`, `E(s_{i+1}-1) = (E(s_i-1)-p_i+V_i)/2`, where the sample `(A,j)` is uniform over distinct-column matrices and columns, `s_i=|S_i|`, `p_i=P(s_i≥2)`, and `V_i=E[(s_i-2k_i)^2/s_i]` at forks and zero at leaves.

Tasks:
1. Prove the fixed-parent identity for children of sizes `a,b>0`, `s=a+b`: `(a*a+b*b)/s = s/2 + (a-b)^2/(2*s)` (or the exact equivalent in the source).
2. Derive the unconditional recurrence **by finite sums over `(A,j)`**, grouping columns by the candidate set at depth `i` or by tree nodes. Do not assert conditional uniformity without proving the counting equality.
3. Treat singleton leaves explicitly, showing they remain singletons and contribute zero to fork indicators and imbalance.
4. Present the result using `FinitePathData.expectedExcess`, `.forkProb`, and `.expectedImbalance`, with the concrete sample representation. The current theorem `uniform_bound_from_lemmas` expects this exact recurrence.
5. If you use abstract axioms such as 'fork nodes partition all columns', prove these from your model or supply a standalone structurally sound lemma with named integration obligations—do not claim the complete recurrence until those are discharged.

Deliver `P2_SizeRecurrence.lean`, ideally with theorem `concrete_expectedExcess_succ`. Coordinate statement shapes with P1 but do not alter P1's source.
