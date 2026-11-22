import GradientKeySection4
import Mathlib.Probability.Moments.SubGaussian

/-!
# P5: uniform inserted-row tail, work in progress

This is an *uncompiled* extension of `GradientKeySection4.lean` version 4.
It proposes a proof script for an algebraic product-factorization statement for the bits at the
unique columns of a fixed feasible deleted-row table, based solely on the
existing bit-flip equivalences. It also gives a proof script for the zero-free-bits case of
the requested tail inequality.

The nonzero-free-bits concentration estimate is **not yet formalized**.
No proof gaps are disguised as declarations or assumptions.

Mathematically, for `F = uniqueIn B S`, `f = F.card`, `s = S.card` and
`Y(x) = ∑ a ∈ F, signedBit x.1 a`, the existing
`all_signs_eq_unique_signs` yields `insertedImbalance x.1 S = Y(x)^2/s`.
The product factorization below gives

  E[exp(t*Y)] = ((exp t + exp (-t))/2)^f.

For `f > 0`, Hoeffding's lemma / `cosh t ≤ exp(t²/2)` and the finite
Chernoff bound yield

  P[Y² > z*s] ≤ 2 exp(-z*s/(2*f)) ≤ 2 exp(-z/2),

because `f ≤ s`. Transferring this analytic argument to Lean is the
remaining open subtask. This file does not claim the desired theorem.
-/

noncomputable section

namespace GradientKey.RowDeletion

open Finset

variable {n m : ℕ}

/-- The missing-row coordinate is complemented by `flipExtension`. -/
private theorem flipExtension_self_eval
    (B : RemainingTable n m) (a : Fin m) (ha : UniqueColumn B a)
    (x : Extension B) :
    ((flipExtension B a ha) x).1 a = !(x.1 a) := by
  classical
  simp [flipExtension, flipBit]

/-- Other coordinates are unchanged by a flip of a unique column. -/
private theorem flipExtension_other_eval
    (B : RemainingTable n m) (a : Fin m) (ha : UniqueColumn B a)
    (x : Extension B) (b : Fin m) (hba : b ≠ a) :
    ((flipExtension B a ha) x).1 b = x.1 b := by
  classical
  simp [flipExtension, flipBit, hba]

/-- A symmetry of a finite uniform fibre makes its chosen bit exactly fair,
including after weighting by any function of the *other* coordinates.
This is the finite-sum ingredient that proves joint independence. -/
theorem weighted_unique_bit_factor
    (B : RemainingTable n m) (a : Fin m) (ha : UniqueColumn B a)
    (w : Extension B → ℝ)
    (hw : ∀ x, w ((flipExtension B a ha) x) = w x)
    (φ : Bool → ℝ) :
    (∑ x : Extension B, w x * φ (x.1 a)) =
      ((φ true + φ false) / 2) * (∑ x : Extension B, w x) := by
  classical
  let e := flipExtension B a ha
  have hEval : ∀ x : Extension B, (e x).1 a = !(x.1 a) := by
    intro x
    exact flipExtension_self_eval B a ha x
  have hSwap :
      (∑ x : Extension B, w x * φ (x.1 a)) =
        (∑ x : Extension B, w x * φ (!(x.1 a))) := by
    calc
      (∑ x : Extension B, w x * φ (x.1 a)) =
          ∑ x : Extension B, w (e x) * φ ((e x).1 a) :=
            (Equiv.sum_comp e (fun x => w x * φ (x.1 a))).symm
      _ = ∑ x : Extension B, w x * φ (!(x.1 a)) := by
        apply Finset.sum_congr rfl
        intro x _
        rw [show e x = (flipExtension B a ha) x from rfl, hw x, hEval x]
  have hTwo :
      (∑ x : Extension B, w x * φ (x.1 a)) +
      (∑ x : Extension B, w x * φ (!(x.1 a))) =
        (φ true + φ false) * (∑ x : Extension B, w x) := by
    rw [← Finset.sum_add_distrib]
    calc
      (∑ x : Extension B,
          (w x * φ (x.1 a) + w x * φ (!(x.1 a)))) =
          ∑ x : Extension B, (φ true + φ false) * w x := by
            apply Finset.sum_congr rfl
            intro x _
            cases h : x.1 a <;> simp [h] <;> ring
      _ = (φ true + φ false) * (∑ x : Extension B, w x) := by
        rw [Finset.mul_sum]
  rw [← hSwap] at hTwo
  linarith

/-- All finite joint moments of unique-column bits factor into the product
of their individual fair-bit moments. In particular the bits are jointly
independent under uniform counting on `Extension B`, not just orthogonal. -/
theorem unique_bit_product_factor
    (B : RemainingTable n m) (φ : Fin m → Bool → ℝ) :
    ∀ F : Finset (Fin m),
      (∀ a ∈ F, UniqueColumn B a) →
      (∑ x : Extension B, ∏ a ∈ F, φ a (x.1 a)) =
        (Fintype.card (Extension B) : ℝ) *
          (∏ a ∈ F, (φ a true + φ a false) / 2) := by
  classical
  intro F
  induction F using Finset.induction_on with
  | empty =>
      intro _
      simp
  | @insert a F ha ih =>
      intro hunique
      have haUnique : UniqueColumn B a :=
        hunique a (Finset.mem_insert_self a F)
      have hFUnique : ∀ b ∈ F, UniqueColumn B b := by
        intro b hb
        exact hunique b (Finset.mem_insert_of_mem hb)
      have hInvariant :
          ∀ x : Extension B,
            (∏ b ∈ F, φ b (((flipExtension B a haUnique) x).1 b)) =
              (∏ b ∈ F, φ b (x.1 b)) := by
        intro x
        apply Finset.prod_congr rfl
        intro b hb
        have hba : b ≠ a := by
          intro h
          exact ha (h ▸ hb)
        rw [flipExtension_other_eval B a haUnique x b hba]
      have hOne := weighted_unique_bit_factor B a haUnique
          (fun x : Extension B => ∏ b ∈ F, φ b (x.1 b))
          hInvariant (φ a)
      calc
        (∑ x : Extension B, ∏ b ∈ insert a F, φ b (x.1 b)) =
            ∑ x : Extension B,
              (∏ b ∈ F, φ b (x.1 b)) * φ a (x.1 a) := by
                apply Finset.sum_congr rfl
                intro x _
                simp [Finset.prod_insert, ha, mul_comm]
        _ = ((φ a true + φ a false) / 2) *
              (∑ x : Extension B, ∏ b ∈ F, φ b (x.1 b)) := hOne
        _ = (Fintype.card (Extension B) : ℝ) *
              (∏ b ∈ insert a F, (φ b true + φ b false) / 2) := by
                rw [ih hFUnique, Finset.prod_insert ha]
                ring

/-- Exact finite exponential moment of the unique-column sign sum.
Unlike a bound obtained from pairwise second moments, this contains
all the information required for Hoeffding/Chernoff. -/
theorem unique_sign_mgf_exact
    (B : RemainingTable n m) (S : Finset (Fin m)) (t : ℝ) :
    (∑ x : Extension B,
      Real.exp (t * (∑ a ∈ uniqueIn B S, signedBit x.1 a))) =
      (Fintype.card (Extension B) : ℝ) *
        ((Real.exp t + Real.exp (-t)) / 2) ^ (uniqueIn B S).card := by
  classical
  let F := uniqueIn B S
  let φ : Fin m → Bool → ℝ :=
    fun _ b => Real.exp (t * if b then (1 : ℝ) else -1)
  have hUnique : ∀ a ∈ F, UniqueColumn B a := by
    intro a ha
    exact (Finset.mem_filter.mp ha).2
  have hFactor := unique_bit_product_factor B φ F hUnique
  have hExp : ∀ x : Extension B,
      Real.exp (t * (∑ a ∈ F, signedBit x.1 a)) =
        ∏ a ∈ F, φ a (x.1 a) := by
    intro x
    rw [Finset.mul_sum, Real.exp_sum]
    apply Finset.prod_congr rfl
    intro a _
    simp only [φ, signedBit]
  calc
    (∑ x : Extension B,
        Real.exp (t * (∑ a ∈ uniqueIn B S, signedBit x.1 a))) =
        ∑ x : Extension B, ∏ a ∈ F, φ a (x.1 a) := by
          apply Finset.sum_congr rfl
          intro x _
          exact hExp x
    _ = (Fintype.card (Extension B) : ℝ) *
          (∏ a ∈ F, (φ a true + φ a false) / 2) := hFactor
    _ = (Fintype.card (Extension B) : ℝ) *
          ((Real.exp t + Real.exp (-t)) / 2) ^
            (uniqueIn B S).card := by
          congr 1
          have hφ : ∀ a, (φ a true + φ a false) / 2 =
              (Real.exp t + Real.exp (-t)) / 2 := by
            intro a
            simp only [φ, if_true, Bool.false_eq_true, if_false, mul_one, mul_neg]
          rw [Finset.prod_congr rfl (fun a _ => hφ a), Finset.prod_const]

/-- Signed ones-minus-zeros count, reproved locally because version 4
keeps its corresponding auxiliary lemma private to its source file. -/
private theorem signed_sum_count
    (x : Fin m → Bool) (T : Finset (Fin m)) :
    (∑ a ∈ T, signedBit x a) =
      2 * (insertedOnes x T : ℝ) - (T.card : ℝ) :=
  signed_sum_eq_counts x T

/-- The exact paper identity `s - 2*k = f - 2*Z`, where `Z` is the
number of inserted ones on unique columns and the pair contributions
have cancelled. The underlying uniformity has no role in this identity. -/
theorem inserted_ones_balance_eq_unique
    (B : RemainingTable n m) (S : Finset (Fin m))
    (hclosed : PairClosed B S) (x : Extension B) :
    (S.card : ℝ) - 2 * (insertedOnes x.1 S : ℝ) =
      ((uniqueIn B S).card : ℝ) -
        2 * (insertedOnes x.1 (uniqueIn B S) : ℝ) := by
  have hsum := all_signs_eq_unique_signs B x.1 x.2 S hclosed
  rw [signed_sum_count x.1 S,
    signed_sum_count x.1 (uniqueIn B S)] at hsum
  linarith

/-- The source's duplicate-pair cancellation gives zero imbalance when
there are no unique columns. This includes the paper's `f = 0` case. -/
theorem insertedImbalance_zero_of_no_unique
    (B : RemainingTable n m) (S : Finset (Fin m))
    (hclosed : PairClosed B S)
    (hzero : (uniqueIn B S).card = 0)
    (x : Extension B) :
    insertedImbalance x.1 S = 0 := by
  rw [insertedImbalance_eq_signed,
    all_signs_eq_unique_signs B x.1 x.2 S hclosed]
  rw [Finset.card_eq_zero.mp hzero]
  simp

/-- Finite uniform probability; separate from the v4 file's private
`finiteAverage` definition. A nonempty fibre is assumed by consumers. -/
noncomputable def finiteProb {Ω : Type*} [Fintype Ω]
    (P : Ω → Prop) [DecidablePred P] : ℝ :=
  ((Finset.univ.filter P).card : ℝ) / (Fintype.card Ω : ℝ)

/-- The complete fixed-fibre tail assertion in the degenerate case `f=0`. -/
theorem conditional_inserted_tail_zero_free
    (B : RemainingTable n m) [Nonempty (Extension B)]
    (S : Finset (Fin m)) (hclosed : PairClosed B S)
    (hzero : (uniqueIn B S).card = 0)
    (z : ℝ) (hz : 0 ≤ z) :
    finiteProb (fun x : Extension B => z < insertedImbalance x.1 S) = 0 := by
  classical
  have hNo : ∀ x : Extension B, ¬ (z < insertedImbalance x.1 S) := by
    intro x
    rw [insertedImbalance_zero_of_no_unique B S hclosed hzero x]
    exact not_lt.mpr hz
  unfold finiteProb
  have he : (Finset.univ.filter
      (fun x : Extension B => z < insertedImbalance x.1 S)) = ∅ := by
    ext x
    simp [hNo x]
  rw [he]
  simp

end GradientKey.RowDeletion
