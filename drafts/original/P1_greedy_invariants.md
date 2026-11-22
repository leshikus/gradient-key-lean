# P1 — Greedy algorithm invariants, termination and tail bound

## Shared context and non-negotiable rules

Read the attached `article.tex` (Section 4, especially Lemmas 4.1–4.3 and Theorem 4.4), `GradientKeySection4.lean` (version 4, ~1,735 lines), and `GradientKeySection4_STATUS.md` before editing. The article, not an earlier assistant summary, is the source of the mathematical theorem. The Lean file is a **candidate, not compiler-verified**. Preserve the paper's mathematical meaning, including first-in-row-order tie breaking and row-deleted tables with duplicate columns.

**Work in your own named file**; do not overwrite `GradientKeySection4.lean` or another agent's file. Prefer importing the baseline if it compiles. If the baseline is broken, give a minimal isolated module and an integration patch rather than inventing a proof of an unrelated statement. Avoid `sorry`, `admit`, `axiom`, `unsafe`, and unnecessary new hypothesis parameters. Existing hypotheses may appear in a *stated interface* only if you clearly identify which agent must discharge them; they do not count as completion. Test using a pinned Lean 4 + Mathlib project (`lake env lean YourFile.lean`) whenever possible, providing exact command, toolchain revision, and output. If unavailable, say **NOT COMPILED** and do not claim verification. Never hide a compiler failure or silently weaken the target proposition.

Return: (1) standalone Lean source or a precise patch, (2) theorem declarations and their status, (3) dependencies on other agents, (4) actual compilation results/errors, and (5) a minimal merge plan. Minimize changes to unrelated sections.

## Your assignment

You own the **concrete greedy-path model**, not probability or deletion coupling. In `GradientKey.Concrete`, study `Table`, `DistinctColumns`, `ones`, `zeros`, `quality`, `greedyRow`, `candidateStep`, `candidateAt`, `pathDepth`, and `finitePathData`.

Prove:
1. `j` remains in `candidateAt A j ... i`, and candidate sets are nested and nonempty.
2. For every valid table and candidate set occurring on the path with at least two columns, some row has positive quality, and the chosen greedy row splits the set into two nonempty pieces. Verify the precise `List.argmax` tie-breaking: the *first* maximal-quality original row must win; repair only if necessary.
3. The candidate-set size decreases strictly at every fork; a row tested above the current node is constant on the current candidate set, so it cannot be tested again at a later fork.
4. Every valid table reaches a singleton in at most `n` forks, and `pathDepth` equals the number of actual forks / the depth of the selected column.
5. For every sample `ω` and every natural `h`, prove the concrete `hTail` property expected by `Concrete.finitePathData`:
`sampleDepth hn ω ≤ (∑ i ∈ Finset.range h, if 2 ≤ sampleSize hn ω i then (1:ℝ) else 0) + ((sampleSize hn ω h:ℝ)-1)`.
6. Derive a public `FinitePathData` instance **without** an assumed `hTail`.

Check endpoint cases `m=2`, `n=1`, `m=2^n`, and `h>n`. Be careful: the greedy choice is implemented over all original rows, but row reuse must be *proved impossible* rather than assumed. Deliver `P1_GreedyPath.lean` and the narrow integration patch.
