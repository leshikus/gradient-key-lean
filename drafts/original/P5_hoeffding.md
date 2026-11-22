# P5 — Prove the concentration half of Lemma 4.2

## Shared context and non-negotiable rules

Read the attached `article.tex` (Section 4, especially Lemmas 4.1–4.3 and Theorem 4.4), `GradientKeySection4.lean` (version 4, ~1,735 lines), and `GradientKeySection4_STATUS.md` before editing. The article, not an earlier assistant summary, is the source of the mathematical theorem. The Lean file is a **candidate, not compiler-verified**. Preserve the paper's mathematical meaning, including first-in-row-order tie breaking and row-deleted tables with duplicate columns.

**Work in your own named file**; do not overwrite `GradientKeySection4.lean` or another agent's file. Prefer importing the baseline if it compiles. If the baseline is broken, give a minimal isolated module and an integration patch rather than inventing a proof of an unrelated statement. Avoid `sorry`, `admit`, `axiom`, `unsafe`, and unnecessary new hypothesis parameters. Existing hypotheses may appear in a *stated interface* only if you clearly identify which agent must discharge them; they do not count as completion. Test using a pinned Lean 4 + Mathlib project (`lake env lean YourFile.lean`) whenever possible, providing exact command, toolchain revision, and output. If unavailable, say **NOT COMPILED** and do not claim verification. Never hide a compiler failure or silently weaken the target proposition.

Return: (1) standalone Lean source or a precise patch, (2) theorem declarations and their status, (3) dependencies on other agents, (4) actual compilation results/errors, and (5) a minimal merge plan. Minimize changes to unrelated sections.

## Your assignment

You own the **tail inequality**, independent of greedy-tree behavior. Work with a fixed feasible deleted-row table `B` and `RowDeletion.Extension B` under its finite uniform distribution. Version 4 already proves `conditional_inserted_imbalance_exact`; do not redo only the mean bound.

For nonempty `S : Finset (Fin m)` with `PairClosed B S`, let `s=S.card`, `F=uniqueIn B S`, `f=F.card`, and `v(x)=insertedImbalance x S`. Prove the exact paper bound for every real `z>0`:

`finiteProb (fun x : Extension B => z < insertedImbalance x.1 S) ≤ 2 * Real.exp (-z/2)`.

Required subtasks:
1. Derive a product representation / independence of the free bits on unique columns and independently oriented duplicate pairs **from uniformity on `Extension B`**. Existing bit-flip involutions prove moments but not concentration by themselves.
2. Show duplicated pairs contribute one 0 and one 1, and `s-2k = f-2Z`, where `Z` is a sum of `f` independent Bernoulli(1/2) bits.
3. Handle `f=0` exactly (`v=0`), and otherwise apply/formalize Hoeffding `P(|Z-f/2|>sqrt(z*s)/2)≤2 exp(-z*s/(2*f))≤2 exp(-z/2)`.
4. Use Mathlib's appropriate Hoeffding/SubGaussian support if it matches the exact statement; otherwise give a finite Chernoff/mgf proof without introducing a new axiom. Keep all strict-vs-nonstrict comparisons correct.
5. Ensure eventual transfer via P3 to `U_r` is possible: expose the bound as a finite fibre statement independent of `j₀`.

Deliver `P5_InsertedRowTail.lean` and a concise description of the Mathlib probability APIs you actually verified.
