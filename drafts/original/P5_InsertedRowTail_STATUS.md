# P5 — inserted-row concentration: handoff and verification status

**Status: PARTIAL / NOT COMPILED.** `P5_InsertedRowTail.lean` is an isolated candidate extension to `GradientKeySection4.lean` v4. The final inequality for positive `f` has **not** been established in Lean. No claim of formal verification should be made.

## Source compatibility

- The paper's `article(6).tex`, Section 4, Lemma 4.2, supplies the target; the bound is the original `2 * exp (-z/2)` for every `z > 0`.
- `GradientKeySection4.lean` v4 was inspected through Files Library search/read, but its raw contents could not be mounted in this runtime. Its exact definitions used here are `RemainingTable`, `SameColumn`, `ValidExtension`, `Extension`, `UniqueColumn`, `flipExtension`, `signedBit`, `uniqueIn`, `PairClosed`, `insertedOnes`, `insertedImbalance`, `all_signs_eq_unique_signs`, and `insertedImbalance_eq_signed`.
- The v4 `finiteAverage` is declared **private**, so the P5 module defines its own `finiteProb` as `(univ.filter P).card / Fintype.card Ω`. This makes its type independent of the sampled column `j₀`.
- `GradientKeySection4_STATUS.md` was not found among the accessible files.

## Candidate declarations (all require compiler checking)

1. `weighted_unique_bit_factor`: finite-sum symmetry of a single free bit under `flipExtension` (with any weight function invariant under that flip).
2. `unique_bit_product_factor`: the joint product law of any finite set of unique-column bits, derived by induction from (1). This is the appropriate independence statement, stronger than uncorrelated signs.
3. `unique_sign_mgf_exact`: unnormalized finite moment generating function `∑ exp(tY) = |Extension B| * ((exp t + exp(-t))/2)^f` for `Y` the sum of signed unique bits.
4. `inserted_ones_balance_eq_unique`: exact `s - 2k = f - 2Z` identity, using the baseline pair cancellation; `Z = insertedOnes x (uniqueIn B S)`.
5. `insertedImbalance_zero_of_no_unique`: exact `v=0` when `f=0` and `PairClosed B S`.
6. `conditional_inserted_tail_zero_free`: probability zero for `z≥0` in the `f=0` case.

These are **scripts**, not checked theorems. There are no placeholders disguised as proofs.

## Mathematical completion (not yet in Lean)

Let `f = (uniqueIn B S).card`, `s = S.card`, and `Y = ∑_{a∈F} signedBit x a`. On `PairClosed B S`, the v4 cancellation identity gives `insertedImbalance x S = Y²/s`. Since `S` is nonempty, `s>0`.

When `f>0`, the product law gives

    E exp(tY) = ((exp t + exp(-t))/2)^f ≤ exp(f*t²/2).

The last inequality is Hoeffding's lemma for a fair Rademacher bit. Exponential Markov for both `Y` and `-Y`, with `u = sqrt(z*s) > 0` and `t=u/f`, implies

    P(Y² > z*s) = P(|Y| > u)
      ≤ 2 exp(-u²/(2*f))
      = 2 exp(-z*s/(2*f))
      ≤ 2 exp(-z/2),

where the last inequality uses `f ≤ s`. The strict event `Y² > z*s` is a subset of `Y ≥ u` or `-Y ≥ u`, so closed-event Hoeffding bounds suffice. No limiting argument is needed. The case `f=0` is proved separately.

Potential direct Mathlib strategy: equip `Extension B` with its uniform probability measure, use the joint product law to prove `iIndepFun` for the free-bit signs, apply `ProbabilityTheory.hasSubgaussianMGF_of_mem_Icc_of_integral_eq_zero` (or directly establish the mgf from `unique_sign_mgf_exact`), and use `ProbabilityTheory.HasSubgaussianMGF.measure_sum_ge_le_of_iIndepFun` for one tail and the negated signs for the other. Another viable route is a finite Chernoff lemma from the exact mgf, avoiding the measure-theory bridge.

## API documentation examined, not compiled

`Mathlib.Probability.Moments.SubGaussian` online documentation reports these exact identifiers and roles:

- `ProbabilityTheory.hasSubgaussianMGF_of_mem_Icc_of_integral_eq_zero` (Hoeffding lemma on bounded centered variables), returning parameter `((‖b-a‖₊)/2)^2`.
- `ProbabilityTheory.HasSubgaussianMGF.sum_of_iIndepFun` (independent centered sub-Gaussian sums).
- `ProbabilityTheory.HasSubgaussianMGF.measure_sum_ge_le_of_iIndepFun` (one-sided Hoeffding bound).
- `ProbabilityTheory.HasSubgaussianMGF.measure_ge_le` (Chernoff bound for a sub-Gaussian variable).
- `Real.exp_sum` (exponential of a finite sum is a product), in `Mathlib.Analysis.Complex.Exponential`.

Documentation was inspected, but no local Lean toolchain or Mathlib version is present to verify compilation or exact compatibility with the user's pin.

## Actual commands / environment

Attempted from `/mnt/data`:

    lake env lean P5_InsertedRowTail.lean
    # bash: lake: command not found

`command -v lake` and `command -v lean` returned nothing; no mathlib project, revision, or toolchain pin is available. Internet name resolution is disabled in the execution container, so installation was not possible. Result: **NOT COMPILED**; no compilation errors or warnings in Lean can be reported.

## Dependencies and merge plan

1. Place both `GradientKeySection4.lean` (v4) and `P5_InsertedRowTail.lean` in the same pinned Lake project; confirm that the import name resolves. First compile v4, resolving any preexisting errors without editing it in P5's branch.
2. Run `lake env lean P5_InsertedRowTail.lean`; fix syntax/API mismatches before using the declarations. The product-factorization proof depends on v4's `flipExtension` and public duplicate-cancellation theorems.
3. Finish a **real, no-extra-assumptions** theorem with the exact signature:

    theorem conditional_inserted_imbalance_tail
        (B : RemainingTable n m) [Nonempty (Extension B)]
        (S : Finset (Fin m)) (hS : 0 < S.card)
        (hclosed : PairClosed B S) (z : ℝ) (hz : 0 < z) :
        finiteProb (fun x : Extension B =>
          z < insertedImbalance x.1 S) ≤
          2 * Real.exp (-z / 2) := by ...

    Prove it separately for `f=0` and `f>0`, using the above Chernoff argument. **This theorem does not yet exist in P5's Lean source.**
4. P3 can then identify its conditional law with `Extension B`; P10 may import this file and use the resulting bound, with no dependence on `j₀` and no changes to greedy tie-breaking.

The final theorem is not blocked by mathematical uncertainty, but by a nontrivial unimplemented analytic/measure-to-counting step and the lack of a compiler in this environment.
