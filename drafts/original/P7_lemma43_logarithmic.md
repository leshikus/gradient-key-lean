# P7 — Truncated expectations, concavity and Lemma 4.3 logarithmic bound

## Shared context and non-negotiable rules

Read the attached `article.tex` (Section 4, especially Lemmas 4.1–4.3 and Theorem 4.4), `GradientKeySection4.lean` (version 4, ~1,735 lines), and `GradientKeySection4_STATUS.md` before editing. The article, not an earlier assistant summary, is the source of the mathematical theorem. The Lean file is a **candidate, not compiler-verified**. Preserve the paper's mathematical meaning, including first-in-row-order tie breaking and row-deleted tables with duplicate columns.

**Work in your own named file**; do not overwrite `GradientKeySection4.lean` or another agent's file. Prefer importing the baseline if it compiles. If the baseline is broken, give a minimal isolated module and an integration patch rather than inventing a proof of an unrelated statement. Avoid `sorry`, `admit`, `axiom`, `unsafe`, and unnecessary new hypothesis parameters. Existing hypotheses may appear in a *stated interface* only if you clearly identify which agent must discharge them; they do not count as completion. Test using a pinned Lean 4 + Mathlib project (`lake env lean YourFile.lean`) whenever possible, providing exact command, toolchain revision, and output. If unavailable, say **NOT COMPILED** and do not claim verification. Never hide a compiler failure or silently weaken the target proposition.

Return: (1) standalone Lean source or a precise patch, (2) theorem declarations and their status, (3) dependencies on other agents, (4) actual compilation results/errors, and (5) a minimal merge plan. Minimize changes to unrelated sections.

## Your assignment

You own the **analytic finite-probability implication** of the tail part of Lemma 4.3. Work abstractly over a nonempty finite uniform `Ω` with `n` row-indexed random variables `U_r≥0` and events `E_r`, so you do not depend on the concrete tree's implementation.

Assume for now as **interface hypotheses** (to be discharged by P3/P4/P5): `P(U_r>z) ≤ 2 exp(-z/2)` for every `z>0`, `q_r=P(E_r)`, and `∑_r q_r=(n-i)p_i`, with `i<n` and `p_i>0`. Derive, with **no further probability or analysis assumptions**:
1. `E[U_r 1_{E_r}] ≤ φ(q_r)` for `φ(0)=0`, `φ(q)=2q(1+ln(2/q))` when `0<q≤1`. Prove the layer-cake/truncated-expectation bound `∫₀^∞ min(q,2 exp(-z/2)) dz = φ(q)` (or an exactly equivalent discrete finite-probability derivation).
2. Prove `φ` is concave on `[0,1]`, including its limit and definition at `q=0`. Prove finite Jensen: `∑_{r=1}^n φ(q_r) ≤ n φ((∑ q_r)/n)`; handle zeros and `n>0` rigorously.
3. Divide by `n-i` and simplify to `V_i ≤ 2p_i(1+ln(2n/((n-i)p_i)))`.
4. Make clear how P4's greedy comparison and event count instantiate your general theorem.

Do not assume Jensen or the integral equality as axioms. Deliver `P7_TailAggregation.lean` with a reusable theorem and a **separate** list of upstream hypotheses that P3/P4/P5 must prove.
