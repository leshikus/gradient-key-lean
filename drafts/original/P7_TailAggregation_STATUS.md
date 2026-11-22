# P7 — logarithmic aggregation: review status

## Source and build constraints

- Reviewed `article(8).tex`, Section 4 (three lemmas and the main theorem) and the P7 assignment.
- `GradientKeySection4.lean` (version 4) and `GradientKeySection4_STATUS.md` were **not included** among the attachments and are not present in `/mnt/data`. Accordingly this patch does not import or modify the baseline.
- `P7_TailAggregation.lean`: **NOT COMPILED**. Command `cd /mnt/data && lake env lean P7_TailAggregation.lean` returned exit code **127**, output: `bash: line 1: lake: command not found`. `lean` and `lake` are absent from PATH and a local Mathlib project was not present. Network resolution to GitHub was unavailable, so no pinned toolchain was installed.
- **NOT A COMPLETE P7 SOLUTION.** No `sorry`, `admit`, new `axiom`, or `unsafe` were placed in the source; nonetheless all theorem declarations are *candidates* until actually compiled. The tail-to-truncated-expectation implication is still missing.

## Theorem list

| Declaration | Mathematical content | Status |
| --- | --- | --- |
| `phi_zero` | `φ(0)=0` | CANDIDATE, NOT COMPILED |
| `phi_pos_formula` | `φ(q)=2q(1+log(2/q))` for `q>0` | CANDIDATE, NOT COMPILED |
| `phi_continuous` | continuity at `q=0`, in particular | CANDIDATE, NOT COMPILED |
| `phi_concave` | concavity on `[0,∞)`, including zero | CANDIDATE, NOT COMPILED |
| `phi_jensen` | n-term finite Jensen, allowing zeros | CANDIDATE, NOT COMPILED |
| `tailAggregation_of_truncated` | final logarithmic bound from Jensen, count, truncated estimate and greedy mean comparison | CANDIDATE, NOT COMPILED; **assumes `htrunc`** |
| `uniformProb_nonneg` | finite-uniform event probabilities are nonnegative | CANDIDATE, NOT COMPILED |
| `finiteUniform_aggregation` | finite uniform space wrapper for previous result | CANDIDATE, NOT COMPILED; **assumes `htrunc`** |

## Unfinished P7 obligation (NOT upstream)

For finite nonempty Ω, nonnegative U : Ω → ℝ and E : Ω → Prop, with q = uniformProb E, prove

```
∀ z > 0, uniformProb (fun ω => U ω > z) ≤ 2 * Real.exp (-z / 2)
⊢ uniformExpect (fun ω => if E ω then U ω else 0) ≤ phi q
```

For q = 0, the event has zero mass in a finite uniform space, hence the truncated expectation is zero. For q > 0, the standard rigorous real-variable argument is

```
E[U 1_E] = ∫_{0}^{∞} P(E ∩ {U > z}) dz
         ≤ ∫_{0}^{∞} min(q, 2 exp(-z/2)) dz.
```

Since q ≤ 1, set `z₀ := 2*log(2/q) ≥ 0`. The integrand is q up to z₀ and `2*exp(-z/2)` afterwards. Thus

```
∫_{0}^{∞} min(q,2 exp(-z/2)) dz
 = q*z₀ + 4*exp(-z₀/2)
 = 2*q*(1+log(2/q)).
```

Mathlib's `MeasureTheory.lintegral_eq_lintegral_meas_lt` (Layercake), `Real.integral_exp_neg_Ioi` (ImproperIntegrals), and `Real.log_div` / `Real.exp_log` are promising primitives; the real finite-uniform measure and ENNReal/Real conversions will need careful compilation.

## Upstream interfaces

- **P3/P5:** justify `Pr(U_r > z) ≤ 2 exp(-z/2)` for every z>0, including positive-probability row-deleted conditioning and averaging, as in article Lemma 4.2.
- **P4:** justify `S_i^{(-r)} = S_i` on E_r with preserved row-order tie breaking; no row is tested twice along a path; exactly n−i untested rows on a depth-i fork.
- **P4:** provide the pointwise greedy comparison `v_i ≤ (∑_r 1_{E_r} U_r)/(n-i)`; after averaging, this is `hgreedy` in the file.
- **P4:** prove `∑_r Pr(E_r)=(n-i)*p_i`, which instantiates `hcount`.
- **P7 (local, still outstanding):** prove the tail-to-truncation lemma above and eliminate `htrunc` from `finiteUniform_aggregation`.

## Minimal merge plan

1. Run from the actual pinned Lean4 + Mathlib project: `lake env lean P7_TailAggregation.lean`. Fix all syntax/API errors first, documenting exact compiler output and toolchain revision.
2. Complete the missing P7 tail-to-truncation implication. It is **not** to be supplied by P3/P4/P5.
3. Import the compiled P7 module into the baseline. In Lemma 4.3, instantiate Ω as the nonempty finite set of admissible (A,j) pairs, E_r as the depth-i fork / untested-row event, and U_r as the imbalance in the row-deleted candidate set.
4. Feed the P3/P5 tail bound and P4 count/coupling/greedy inequalities into the new assembled theorem; retain first-in-row-order tie breaking and duplicate-column row deletions.
5. Recompile integrated target, check for `sorry`, `admit`, `axiom`, `unsafe`, and verify that the statement matches the paper (no strengthened hypotheses).
