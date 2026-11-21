# MASTER PROMPT — Integrate and formally verify Section 4 (P0–P10)

You are a Lean 4/Mathlib formalization and mathematical integration specialist.
Your task is to make a fully compiled, **unconditional** Lean proof of Section 4,
Theorem 4.4 (including (a), (b), (c)), of the **original** `article.tex`.
Use every artifact in this bundle; in particular read the reports and actual
Lean sources, not merely the original task prompts.

## Truthfulness and proof standards

- The mathematical source of truth is the original `article.tex`, which must
  be supplied separately because it was not exportable into this bundle.
- `GradientKeySection4.lean` v4 and P1–P8 are **uncompiled proof candidates**.
  Prior agents had no `lean`, `lake`, or Mathlib. The Python checks are
  independent mathematical tests, not machine verification.
- Preserve exactly the original greedy algorithm: first row of maximum
  quality in original row order on ties; column-distinct input tables;
  duplicate columns allowed on row deletion; no row reuse on genuine paths.
- Never add `sorry`, `admit`, `axiom`, `unsafe`, or a hidden extra theorem
  hypothesis to achieve apparent success. Abstract lemma parameters must all
  be discharged by proved statements in the final concrete theorem.
- Keep corrections local. Use one canonical deleted-path model or prove
  adapters, and avoid duplicate or circular modules.

## Environment / start

P0 proposed Lean `v4.34.1` and Mathlib commit
`d13f23b723b8a846827a245b89c10fc7d3f11612`. Verify compatibility,
produce `lean-toolchain`, `lakefile.toml`, and lock dependencies. Run
`lake env lean GradientKeySection4.lean` **unchanged first** and record actual
compiler diagnostics. Export `finiteAverage` and only required helpers.
Apply and test P9's one-line source correction inside `partner_twice`:
`exact False.elim (hneq hba.symm)` → `exact False.elim (hneq hba)`.
This is necessary but is not asserted sufficient for compilation.

## Work breakdown and important remaining gaps

### P1: Concrete greedy path
Use `P1_GreedyPath.lean`. Prove survival/nesting/nonemptiness of candidate
sets; positive quality when a fork is possible; first maximal-row tie rule;
selected row becomes inactive on descendants; no row reuse; termination
within `n` forks; depth equals actual tests; and the pointwise tail bound
`d ≤ ∑_{i<h} 1_{s_i≥2}+(s_h-1)`. Supply `FinitePathData` without an assumed
`hTail`. Choose either import or patch, not both.

### P2: Lemma 4.1 recurrence
Use `P2_SizeRecurrence.lean`'s fixed-partition finite identity.
Prove `candidateAt A j i` is the fibre of `j ↦ candidateAt A j i`, that
`candidateAt A j (i+1)` is its `(key,bit)` refined fibre, and that abstract
imbalance equals concrete imbalance (zero on singletons). Sum over the
uniform table-column samples to prove
`e_(i+1)=(e_i-p_i+V_i)/2`, with `e_0=m-1`.
The concrete fibre bridge is not yet done.

### P3: Finite conditional uniformity
Use `P3_FiniteFibreCore.lean` and `P3_ConditionalFibre.lean`.
Prove an order-preserving delete/insert row bijection at every fixed row.
For fixed deleted table `B` and fixed sampled column `j₀`, prove the
conditional distribution of inserted row is uniform on `Extension B`,
retaining the independent `j` coordinate. Handle empty extension fibres.
Use the existing exact mean `E[v | B,j₀]=f/s≤1` when the candidate is
nonempty and pair-closed. Transfer mean and tails to unconditional `U_r`.

### P4: Deleted-path coupling
Use `P4_DeletedPath.lean`, whose remaining row type is
`{k : Fin n // k ≠ r}`; P3/baseline use `Fin (n-1)`. Construct the
order-preserving equivalence and transport candidate and PairClosed facts.
Deleted matrices may have identical columns and terminate at a nonsingleton
candidate set, which stays constant after termination. On `E_r` (fork at
depth `i`, row `r` not tested above), prove prefix agreement,
`S_i^{(-r)}=S_i`, and `U_r=v_r(S_i)`; prove exactly `n-i` unused rows and
`v_i 1_{s_i≥2} ≤ (∑_r 1_{E_r}U_r)/(n-i)` for `i<n`.
Remove P4's conditional P1 inputs using P1 invariants.

### P5: Complete Lemma 4.2 Hoeffding tail — still unfinished
Use `P5_InsertedRowTail.lean`. The intended final bound is
`P_{x∈Extension B}(v(x)>z) ≤ 2 exp(-z/2)` for `z>0` and nonempty pair-closed
`S`. Duplicate pairs cancel; free unique-column bits are independently
uniform. Write `s=|S|`, `f=|uniqueIn B S|`, `s-2k=f-2Z`, and signed sum `Y`.
Prove `E exp(tY)=((exp t+exp(-t))/2)^f ≤ exp(f t²/2)` and apply finite
Chernoff/Hoeffding to obtain `2 exp(-z s/(2f)) ≤ 2 exp(-z/2)`.
Handle `f=0` exactly. The actual positive-`f` final theorem was NOT proved
in the existing P5 file. Do not assume it.

### P6: First Lemma 4.3 bound
Use `P6_MeanBound.lean`. Discharge its explicit P1/P3/P4 interfaces
(`unusedCount`, `greedyLower`, `fibreEquiv`, `fibreTransport`) and derive
`V_i ≤ n/(n-i)` without any extra assumptions for `i<n`.

### P7: Logarithmic Lemma 4.3 bound — still unfinished
Use `P7_TailAggregation.lean`. Prove the missing **local** tail-to-truncated
expectation bridge, eliminating `htrunc`: for `q=P(E)` and `U≥0` with
`P(U>z)≤2 exp(-z/2)` prove
`E[U 1_E]≤φ(q)`, where `φ(0)=0` and
`φ(q)=2q(1+log(2/q))` for `0<q≤1`.
An approach is layer-cake with integrand `min(q,2 exp(-z/2))`, split at
`2log(2/q)`. Prove continuity/concavity at zero, Jensen for `n` events,
`∑_r P(E_r)=(n-i)p_i`, and finally
`V_i ≤ 2p_i(1+log(2n/((n-i)p_i)))` for `p_i>0`.
When `p_i=0`, prove `V_i=0` from the concrete definition.

### P8: Theorem 4.4 deterministic aggregation
Use `P8_Theorem44.lean` and its audit. Its conditional telescoping proof
starts from `e_(i+1)=(e_i-p_i+V_i)/2`, `e_0=m-1`, and
`t ≤ ∑_{i<h}p_i+e_h`, yielding
`2^h e_h=m-1+∑_{i<h}2^i(V_i-p_i)`.
Choose `ℓ=Nat.log 2 m`; show `1≤ℓ≤n` from `2≤m≤2^n`, prove the
logarithmic binary-window chord bound, and preserve the strict (a),(b)
conclusions using `∑_{i<ℓ}2^(i-ℓ)<1`. For (c), prove the original
`n≥2ℓ-2` condition with correct natural-number arithmetic.
Do not strengthen any assumptions or alter constants from the paper.

### P9: Adversarial audit
Apply `P9_patch.diff` after checking it. The exhaustive Python P9 checks
found no mathematical counterexample, but flagged incomplete conditional
interfaces and the baseline type mismatch above. Verify first-row ties,
row deletion order, duplicate classes, empty fibres, denominators,
`f=0`, `p_i=0`, `n=1`, `m=2`, `m=2^n`, and `n=ℓ`. Python tests do not
replace Lean compilation.

### P10: Finish the concrete theorem
Prove `Sample n m` nonempty under `2≤m≤2^n`; identify
`E(sampleDepth)` with the article's literal `t_{n,m}(G)`, not a surrogate.
Discharge baseline theorem parameters `hTail`, `hTransition`, `hVMean`,
`hVTail`, recurrence/probability hypotheses, and any event/conditioning
parameters. The final theorem may have only the article's parameter
assumptions, plus the explicit (c) condition.

## Validation and output

Run `lake build` and `lake env lean` on every final module. Run the supplied
Python regression scripts as supplementary checks. Inspect and eliminate
unexpected `sorry`, `admit`, `axiom`, `unsafe`, `native_decide` and print
`#print` and `#print axioms` on the final theorem. Compiler errors must be
reported exactly, not inferred from missing toolchains.

Produce `P10_Integrated/` with all Lean sources, pin files, build logs,
version info, theorem signature, axiom report, integration patch, README,
summary of original P0–P9 contributions, a verified/unresolved table,
and a statement of whether the unconditional Theorem 4.4 was actually
kernel-checked. If incomplete, provide the smallest outstanding goals and
maximum reproducible partial progress; never claim complete verification.
