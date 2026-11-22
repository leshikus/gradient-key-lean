# P0 — Build, compile and repair the existing Lean baseline

## Shared context and non-negotiable rules

Read the attached `article.tex` (Section 4, especially Lemmas 4.1–4.3 and Theorem 4.4), `GradientKeySection4.lean` (version 4, ~1,735 lines), and `GradientKeySection4_STATUS.md` before editing. The article, not an earlier assistant summary, is the source of the mathematical theorem. The Lean file is a **candidate, not compiler-verified**. Preserve the paper's mathematical meaning, including first-in-row-order tie breaking and row-deleted tables with duplicate columns.

**Work in your own named file**; do not overwrite `GradientKeySection4.lean` or another agent's file. Prefer importing the baseline if it compiles. If the baseline is broken, give a minimal isolated module and an integration patch rather than inventing a proof of an unrelated statement. Avoid `sorry`, `admit`, `axiom`, `unsafe`, and unnecessary new hypothesis parameters. Existing hypotheses may appear in a *stated interface* only if you clearly identify which agent must discharge them; they do not count as completion. Test using a pinned Lean 4 + Mathlib project (`lake env lean YourFile.lean`) whenever possible, providing exact command, toolchain revision, and output. If unavailable, say **NOT COMPILED** and do not claim verification. Never hide a compiler failure or silently weaken the target proposition.

Return: (1) standalone Lean source or a precise patch, (2) theorem declarations and their status, (3) dependencies on other agents, (4) actual compilation results/errors, and (5) a minimal merge plan. Minimize changes to unrelated sections.

## Your assignment

You own **compilation, project setup and Lean API compatibility**, not the mathematical proof gaps. Build a reproducible Lean 4/Mathlib project for version 4 and compile the original source exactly as supplied before changing it.

Tasks:
1. Establish `lean-toolchain`, `lakefile.toml` (or compatible lake config), and a clean import environment; report exact versions.
2. Run `lake env lean GradientKeySection4.lean`, collect **all** errors and group them by root cause (parsing, namespace scope, Mathlib theorem mismatch, actual proof failure).
3. Fix minimally in `P0_BaselineFixed.lean`. Prioritize `List.argmax`, `Finset.sum_involution`, `Equiv.sum_comp`, the `finiteAverage_*` lemmas, natural-number `Nat.log`, the chord/log proof, and split-size algebra.
4. Keep all existing theorem statements, especially `theorem_4_4_all_from_probabilistic_lemmas` and `conditional_inserted_imbalance_exact`, logically unchanged. If a theorem cannot be fixed quickly, isolate its exact error; do not replace it with an unproved lemma or a stronger assumption.
5. Identify which `private` declarations (`finiteAverage` in particular) other agents need exported via a public API, and provide a minimal export patch.

Acceptance: a reproducible build where all of the existing source compiles, or an accurate line-by-line blocker report and a smaller compiling core; zero invented proof obligations. You are the only agent authorized to propose broad syntactic repairs to the baseline.
