# Parallel Lean 4 formalization — agent prompt pack

Source: `article.tex`, Section 4, Lemmas 4.1–4.3, Theorem 4.4. Baseline: `GradientKeySection4.lean` (v4); status `GradientKeySection4_STATUS.md`. The baseline has **not** been compiled and has explicit hypotheses in the main theorem. The goal is a conditional-proof-to-unconditional-proof upgrade, not a numeric simulation.

## Dispatch
Launch **P0–P9 concurrently**, ideally each in its own conversation / working directory with copies of all three source files. Each `.md` file is a standalone prompt. Do not let multiple agents edit the baseline. After agent reports arrive, run **P10** (not concurrent with the other agents) to merge/compile.

## Dependency sketch
- **P0**: build infrastructure and common API exposure; all agents benefit but can develop independently.
- **P1** greedy path → **P4** row-deleted coupling, **P6** mean, **P10**.
- **P2** recurrence → **P10**.
- **P3** finite conditional law → **P6**, **P7** through transferred tails, **P10**.
- **P4** pair closure/coupling → **P6**, **P7** and **P10**.
- **P5** conditional concentration → **P7** via P3 bridge, **P10**.
- **P6** mean estimate → **P10**.
- **P7** logarithmic estimate → **P10**.
- **P8** independent final algebra → **P10**.
- **P9** auditor → **P10**, and send early serious issues to affected agents.

## Boundary interfaces / code map
- `GradientKey.Concrete`: `Table`, `DistinctColumns`, `ValidTable`, `Sample`, `greedyRow`, `candidateAt`, `pathDepth`, `finitePathData` (~lines 979–1085).
- `GradientKey.RowDeletion`: `RemainingTable`, `ValidExtension`, `Extension`, `PairClosed`, `conditional_inserted_imbalance_exact` (~lines 904–1654).
- Finite averaging: `FinitePathData`, `expectedExcess`, `forkProb`, `expectedImbalance`, `expectedTail` (~lines 704–890). Some finite average helpers are `private`; P0 should resolve public API needs.
- `mean_imbalance_from_unused_rows` (~lines 1667–1735) already provides the abstract mean averaging.
- `theorem_4_4_all_from_probabilistic_lemmas` (~line 642) is the conditional final target; eliminate its *need* for extra hypotheses via a concrete theorem, rather than deleting mathematically correct abstract interfaces.

## Acceptance
No unverified claim of Lean success. Require each agent's Lean file(s), exact toolchain and compilation status, theorem statement(s), proof obligations that remain, and a minimal integration patch. The highest-value deliverable is a compiler-checked unconditional Theorem 4.4 matching the article, not merely a large file without `sorry`.


---

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


---

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


---

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


---

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


---

# P4 — Greedy paths after deleting a row, pair closure and coupling

## Shared context and non-negotiable rules

Read the attached `article.tex` (Section 4, especially Lemmas 4.1–4.3 and Theorem 4.4), `GradientKeySection4.lean` (version 4, ~1,735 lines), and `GradientKeySection4_STATUS.md` before editing. The article, not an earlier assistant summary, is the source of the mathematical theorem. The Lean file is a **candidate, not compiler-verified**. Preserve the paper's mathematical meaning, including first-in-row-order tie breaking and row-deleted tables with duplicate columns.

**Work in your own named file**; do not overwrite `GradientKeySection4.lean` or another agent's file. Prefer importing the baseline if it compiles. If the baseline is broken, give a minimal isolated module and an integration patch rather than inventing a proof of an unrelated statement. Avoid `sorry`, `admit`, `axiom`, `unsafe`, and unnecessary new hypothesis parameters. Existing hypotheses may appear in a *stated interface* only if you clearly identify which agent must discharge them; they do not count as completion. Test using a pinned Lean 4 + Mathlib project (`lake env lean YourFile.lean`) whenever possible, providing exact command, toolchain revision, and output. If unavailable, say **NOT COMPILED** and do not claim verification. Never hide a compiler failure or silently weaken the target proposition.

Return: (1) standalone Lean source or a precise patch, (2) theorem declarations and their status, (3) dependencies on other agents, (4) actual compilation results/errors, and (5) a minimal merge plan. Minimize changes to unrelated sections.

## Your assignment

You own the **row-deleted greedy algorithm and path agreement** used in Lemma 4.3. The current `Concrete` path assumes a valid full table; the paper explicitly allows repeated columns after deleting a row. Implement that separate case correctly.

Tasks:
1. Define a greedy path on an arbitrary binary table `B : RemainingTable ...` whose columns may repeat: at a node, test the first maximum-quality row if a splitting row exists; otherwise stop and retain a terminal candidate set that may have size >1. After termination the candidate set remains unchanged at all later depths.
2. Define `deletedCandidate A r j i` as `S_i^{(-r)}` and `U_r = v_r(S_i^{(-r)})` with correct handling of always-nonempty candidate sets.
3. Show every `S_i^{(-r)}` is `RowDeletion.PairClosed (deleteRow A r) (S_i^{(-r)})`: two equal columns in the reduced matrix cannot be separated by any reduced row.
4. Prove *prefix coupling*: on event `E_r` that the full valid greedy path has a fork at depth `i` and row `r` was not tested at depths `<i`, the reduced path matches the full path at every depth `≤i`. Preserve the first-by-original-row-order tie-breaking after deletion.
5. Establish that on `E_r` the full path's `v_r(S_i)` equals `U_r`, and exactly `n-i` rows are unused on any full path with `s_i≥2`.
6. Supply the pointwise greedy comparison `v_i 1_{s_i≥2} ≤ (1/(n-i)) ∑_r 1_{E_r} U_r` for `i<n`.

Deliver `P4_DeletedPath.lean` with explicit lemmas suitable for P6/P7. Do not assume deleted columns remain distinct.


---

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


---

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


---

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


---

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


---

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


---

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
