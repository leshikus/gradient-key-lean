# P6 — Assemble the first estimate of Lemma 4.3

## Shared context and non-negotiable rules

Read the attached `article.tex` (Section 4, especially Lemmas 4.1–4.3 and Theorem 4.4), `GradientKeySection4.lean` (version 4, ~1,735 lines), and `GradientKeySection4_STATUS.md` before editing. The article, not an earlier assistant summary, is the source of the mathematical theorem. The Lean file is a **candidate, not compiler-verified**. Preserve the paper's mathematical meaning, including first-in-row-order tie breaking and row-deleted tables with duplicate columns.

**Work in your own named file**; do not overwrite `GradientKeySection4.lean` or another agent's file. Prefer importing the baseline if it compiles. If the baseline is broken, give a minimal isolated module and an integration patch rather than inventing a proof of an unrelated statement. Avoid `sorry`, `admit`, `axiom`, `unsafe`, and unnecessary new hypothesis parameters. Existing hypotheses may appear in a *stated interface* only if you clearly identify which agent must discharge them; they do not count as completion. Test using a pinned Lean 4 + Mathlib project (`lake env lean YourFile.lean`) whenever possible, providing exact command, toolchain revision, and output. If unavailable, say **NOT COMPILED** and do not claim verification. Never hide a compiler failure or silently weaken the target proposition.

Return: (1) standalone Lean source or a precise patch, (2) theorem declarations and their status, (3) dependencies on other agents, (4) actual compilation results/errors, and (5) a minimal merge plan. Minimize changes to unrelated sections.

## Your assignment

You own the **mean part of Lemma 4.3**, `V_i ≤ n/(n-i)` for every `0≤i<n`. Avoid reproving the finite second-moment estimate, which version 4 provides as `RowDeletion.conditional_inserted_imbalance_le_one`, or the finite algebra step `mean_imbalance_from_unused_rows`.

Tasks:
1. Define in a concrete sample space the events `E_r`, random variables `U_r= v_r(S_i^{(-r)})`, actual imbalance `v_i`, and its average `V_i`.
2. Establish `0≤U_r`, conditional expectation `E(U_r | deleteRow A r=B, j=j₀) ≤1`, then `E U_r≤1` using the finite fibre law provided by P3. The candidate set used in conditional expectation must depend only on `(B,j₀)`; use the pair closure supplied by P4.
3. Prove the pointwise greedy comparison and averaging, using exactly `n-i` unused rows (P1/P4).
4. Instantiate existing `mean_imbalance_from_unused_rows` with concrete `Ω=Concrete.Sample n m`, or produce a minimal replacement if the theorem's interface is incorrect.
5. Return theorem `expectedImbalance_le_rows (i<n) : V_i ≤ n/(n-i)` with explicit real coercions and denominator positivity.

This agent can compile the generic finite-averaging algebra before P3/P4 finish; make dependencies explicit but do **not** elevate an assumption-dependent bridge to the status of a completed proof. Deliver `P6_MeanBound.lean`.
