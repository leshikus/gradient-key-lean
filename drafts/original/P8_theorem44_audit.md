# P8 — Independently reconstruct and verify Theorem 4.4

## Shared context and non-negotiable rules

Read the attached `article.tex` (Section 4, especially Lemmas 4.1–4.3 and Theorem 4.4), `GradientKeySection4.lean` (version 4, ~1,735 lines), and `GradientKeySection4_STATUS.md` before editing. The article, not an earlier assistant summary, is the source of the mathematical theorem. The Lean file is a **candidate, not compiler-verified**. Preserve the paper's mathematical meaning, including first-in-row-order tie breaking and row-deleted tables with duplicate columns.

**Work in your own named file**; do not overwrite `GradientKeySection4.lean` or another agent's file. Prefer importing the baseline if it compiles. If the baseline is broken, give a minimal isolated module and an integration patch rather than inventing a proof of an unrelated statement. Avoid `sorry`, `admit`, `axiom`, `unsafe`, and unnecessary new hypothesis parameters. Existing hypotheses may appear in a *stated interface* only if you clearly identify which agent must discharge them; they do not count as completion. Test using a pinned Lean 4 + Mathlib project (`lake env lean YourFile.lean`) whenever possible, providing exact command, toolchain revision, and output. If unavailable, say **NOT COMPILED** and do not claim verification. Never hide a compiler failure or silently weaken the target proposition.

Return: (1) standalone Lean source or a precise patch, (2) theorem declarations and their status, (3) dependencies on other agents, (4) actual compilation results/errors, and (5) a minimal merge plan. Minimize changes to unrelated sections.

## Your assignment

You own the **deterministic final theorem**, independently of the finite greedy proof. Start from the exact hypotheses of Lemmas 4.1 and 4.3, and formalize the paper's Theorem 4.4 *without adding an extra probabilistic assumption*.

Required target: for `2≤m≤2^n`, `ell=Nat.log 2 m`, `t` is the average greedy depth, `e_i=E(s_i-1)`, `p_i=P(s_i≥2)`, and `V_i=E(v_i)`, prove
`t ≤ ell-1 + m*2^(-ell) + ∑_{i<ell} 2^(i-ell) * min(n/(n-i), 2+2*ln(2*n/(n-i)))`,
plus strict bounds (a) `t<log₂ m+2+2 ln(2ell)`, (b) `t<log₂ m+1+(ell-1)/(n-ell+1)`, and (c) `t<log₂ m+2` under `n≥2ell-2`.

Check in particular:
- Correct factor `(e_i-p_i+V_i)/2` and the weighted unrolling.
- `p_i=0 ⇒ V_i=0`, and monotonicity of `p↦p(1+ln(c/p))` for `0<p≤1<c`.
- Derive `ell≥1`, `ell≤n` from hypotheses; ensure all denominators strictly positive.
- Show `ell-1+m/2^ell≤log₂ m`, including powers of two and `m=2`.
- Preserve **strict** `<` in (a), (b), and (c), using `∑ weights <1`.
- Verify that the integer expression `2*ell-2≤n` matches the article (beware `Nat.sub`).

The baseline has `uniform_bound_from_lemmas`, `theorem_4_4_all_from_probabilistic_lemmas`, and natural-log corollaries; compare them against an independent derivation, repair bad proof scripts, and return `P8_Theorem44.lean`. No source-wide refactor.
