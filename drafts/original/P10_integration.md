# P10 — Final integrator: remove theorem hypotheses and compile end-to-end

## Shared context and non-negotiable rules

Read the attached `article.tex` (Section 4, especially Lemmas 4.1–4.3 and Theorem 4.4), `GradientKeySection4.lean` (version 4, ~1,735 lines), and `GradientKeySection4_STATUS.md` before editing. The article, not an earlier assistant summary, is the source of the mathematical theorem. The Lean file is a **candidate, not compiler-verified**. Preserve the paper's mathematical meaning, including first-in-row-order tie breaking and row-deleted tables with duplicate columns.

**Work in your own named file**; do not overwrite `GradientKeySection4.lean` or another agent's file. Prefer importing the baseline if it compiles. If the baseline is broken, give a minimal isolated module and an integration patch rather than inventing a proof of an unrelated statement. Avoid `sorry`, `admit`, `axiom`, `unsafe`, and unnecessary new hypothesis parameters. Existing hypotheses may appear in a *stated interface* only if you clearly identify which agent must discharge them; they do not count as completion. Test using a pinned Lean 4 + Mathlib project (`lake env lean YourFile.lean`) whenever possible, providing exact command, toolchain revision, and output. If unavailable, say **NOT COMPILED** and do not claim verification. Never hide a compiler failure or silently weaken the target proposition.

Return: (1) standalone Lean source or a precise patch, (2) theorem declarations and their status, (3) dependencies on other agents, (4) actual compilation results/errors, and (5) a minimal merge plan. Minimize changes to unrelated sections.

## Your assignment

Start **only after P0–P9 deliver results**. You are the sole agent merging changes into the main file. Treat all agent statements as untrusted until Lean confirms them.

1. Create a reproducible Mathlib project and preserve each agent's source as a separate module. Merge in dependency order: P0 baseline; P1 concrete greedy invariants; P2 transition; P3 finite row fibre law; P4 deleted-path coupling; P5 Hoeffding; P6 mean; P7 logarithmic bound; P8 final analytic theorem; P9 corrections.
2. Avoid circular imports: place shared finite averages, row deletion, and path definitions in small common modules. Replace `private` helpers with minimal public interfaces only where required.
3. Replace the explicit hypotheses `hTail`, `hTransition`, `hVMean`, `hVTail` in `theorem_4_4_from_finite_paths` / the final theorem by proved lemmas about concrete random tables.
4. Define and prove equality of the concrete finite expectation of `sampleDepth` with the article's `t_{n,m}(G)`; show sample space nonempty under `2≤m≤2^n`.
5. Output the unconditional theorem with assumptions only `2≤m≤2^n`, plus the conditional (c) assumption `n≥2ell-2`. Its hypotheses must not include any probabilistic inequality, tree invariant, or conditional distribution result.
6. Run `lake build` and `lake env lean` on **every** module. List all `sorry`, `admit`, `axiom`, `unsafe` and `native_decide` occurrences and explain any unexpected uses. Check `#print axioms` for the final theorem; ordinary Mathlib axioms are acceptable if transparently reported, but no user-introduced axioms.
7. Add small `example` tests for `(n,m)=(1,2),(3,4)` and denominator/edge cases; do not confuse finite computation with the general proof. Preserve exact mathematical definitions.
8. Deliver the `.lean` source tree, version-pinned Lake files, build log, `#print` of theorem signature, and a compact *verified vs. unresolved* checklist. If any component fails, mark the final result incomplete and provide exact remaining goals/errors, never 'proof complete'.

Deliver `P10_Integrated` directory and, only if compilation succeeds, a statement that Theorem 4.4 is machine-checked.
