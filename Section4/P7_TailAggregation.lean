import Mathlib

/-!
P7: analytic aggregation for the logarithmic half of Lemma 4.3.

STATUS: NOT COMPILED. This file is an isolated candidate, since the baseline Lean
file and STATUS file named in the task were not among the supplied attachments.

The *tail -> truncated expectation* lemma has NOT been formalized here.  The
`htrunc` hypothesis in `tailAggregation_of_truncated` is a missing local P7
obligation, not an upstream hypothesis and not a proved consequence of `htail`.
No theorem in this file claims otherwise.
-/

open scoped BigOperators

namespace P7

/-- Extension to zero of `2*q*(1 + log (2/q))`. -/
noncomputable def phi (q : ℝ) : ℝ :=
  2 * (q * (1 + Real.log 2) + Real.negMulLog q)

@[simp] theorem phi_zero : phi 0 = 0 := by
  simp [phi]

/-- The formula in the paper, valid for all strictly positive `q`. -/
theorem phi_pos_formula {q : ℝ} (hq : 0 < q) :
    phi q = 2 * q * (1 + Real.log (2 / q)) := by
  rw [Real.log_div (by norm_num : (2 : ℝ) ≠ 0) (ne_of_gt hq)]
  simp only [phi, Real.negMulLog_eq_neg]
  ring

/-- Includes the correct continuous extension at `q = 0`. -/
theorem phi_continuous : Continuous phi := by
  unfold phi
  exact continuous_const.mul
    ((continuous_id.mul continuous_const).add Real.continuous_negMulLog)

/-- Concavity holds even across `q = 0`, not just on `(0,1]`. -/
theorem phi_concave : ConcaveOn ℝ (Set.Ici (0 : ℝ)) phi := by
  refine ⟨convex_Ici 0, ?_⟩
  intro x hx y hy a b ha hb hab
  have h := Real.concaveOn_negMulLog.2 hx hy ha hb hab
  simp only [smul_eq_mul] at h ⊢
  calc
    a * phi x + b * phi y =
        2 * ((a * x + b * y) * (1 + Real.log 2) +
          (a * Real.negMulLog x + b * Real.negMulLog y)) := by
          unfold phi
          ring
    _ ≤ 2 * ((a * x + b * y) * (1 + Real.log 2) +
          Real.negMulLog (a * x + b * y)) := by
          apply mul_le_mul_of_nonneg_left _ (by norm_num : (0 : ℝ) ≤ 2)
          linarith [h]
    _ = phi (a * x + b * y) := by
          unfold phi
          ring

/-- Finite Jensen, including zero entries, with exactly `n` row indices. -/
theorem phi_jensen {n : ℕ} (hn : 0 < n)
    (q : Fin n → ℝ) (hq : ∀ r, 0 ≤ q r) :
    (∑ r : Fin n, phi (q r)) ≤
      (n : ℝ) * phi ((∑ r : Fin n, q r) / (n : ℝ)) := by
  have hnR : (0 : ℝ) < (n : ℝ) := by exact_mod_cast hn
  have hn0 : (n : ℝ) ≠ 0 := ne_of_gt hnR
  let w : Fin n → ℝ := fun _ => (n : ℝ)⁻¹
  have hw0 : ∀ r ∈ (Finset.univ : Finset (Fin n)), 0 ≤ w r := by
    intro r hr
    exact inv_nonneg.mpr (le_of_lt hnR)
  have hw1 : (∑ r : Fin n, w r) = 1 := by
    simp [w, Finset.sum_const, nsmul_eq_mul, hn0]
  have hJ := phi_concave.le_map_sum
    (t := Finset.univ) (w := w) (p := q)
    hw0 hw1 (by intro r hr; exact hq r)
  have hleft : (∑ r : Fin n, w r • phi (q r)) =
      (∑ r : Fin n, phi (q r)) / (n : ℝ) := by
    simp only [smul_eq_mul, w]
    rw [← Finset.mul_sum]
    ring
  have hright : (∑ r : Fin n, w r • q r) =
      (∑ r : Fin n, q r) / (n : ℝ) := by
    simp only [smul_eq_mul, w]
    rw [← Finset.mul_sum]
    ring
  rw [hleft, hright] at hJ
  have hbound := (div_le_iff₀ hnR).mp hJ
  nlinarith [hbound]

/-- Abstract analytic consequence of Jensen and a *separately provided*
    truncated-expectation comparison.  `htrunc` is not derived from the tail
    estimate in this candidate. -/
theorem tailAggregation_of_truncated
    {n i : ℕ} (hi : i < n)
    (q T : Fin n → ℝ) (p V : ℝ)
    (hq : ∀ r, 0 ≤ q r) (hp : 0 < p)
    (hcount : (∑ r : Fin n, q r) = ((n - i : ℕ) : ℝ) * p)
    (htrunc : ∀ r, T r ≤ phi (q r))
    (hgreedy : ((n - i : ℕ) : ℝ) * V ≤ ∑ r : Fin n, T r) :
    V ≤ 2 * p * (1 + Real.log (2 * (n : ℝ) /
      (((n - i : ℕ) : ℝ) * p))) := by
  have hiN : 0 < n - i := Nat.sub_pos_of_lt hi
  have hiR : (0 : ℝ) < ((n - i : ℕ) : ℝ) := by exact_mod_cast hiN
  have hnN : 0 < n := Nat.lt_of_le_of_lt (Nat.zero_le i) hi
  have hnR : (0 : ℝ) < (n : ℝ) := by exact_mod_cast hnN
  have hn0 : (n : ℝ) ≠ 0 := ne_of_gt hnR
  have hid0 : (((n - i : ℕ) : ℝ) * p) ≠ 0 :=
    ne_of_gt (mul_pos hiR hp)
  have hsum : (∑ r : Fin n, T r) ≤ (∑ r : Fin n, phi (q r)) :=
    Finset.sum_le_sum (by intro r hr; exact htrunc r)
  have hj := phi_jensen hnN q hq
  have hfull : ((n - i : ℕ) : ℝ) * V ≤
      (n : ℝ) * phi ((((n - i : ℕ) : ℝ) * p) / (n : ℝ)) := by
    calc
      _ ≤ ∑ r : Fin n, T r := hgreedy
      _ ≤ ∑ r : Fin n, phi (q r) := hsum
      _ ≤ (n : ℝ) * phi ((∑ r : Fin n, q r) / (n : ℝ)) := hj
      _ = _ := by rw [hcount]
  have havg : 0 < (((n - i : ℕ) : ℝ) * p) / (n : ℝ) :=
    div_pos (mul_pos hiR hp) hnR
  have hlogarg :
      (2 : ℝ) / ((((n - i : ℕ) : ℝ) * p) / (n : ℝ)) =
        2 * (n : ℝ) / (((n - i : ℕ) : ℝ) * p) := by
    field_simp [hn0, hid0, ne_of_gt havg]
    <;> ring
  have hrewrite :
      (n : ℝ) * phi ((((n - i : ℕ) : ℝ) * p) / (n : ℝ)) =
      ((n - i : ℕ) : ℝ) *
        (2 * p * (1 + Real.log
          (2 * (n : ℝ) / (((n - i : ℕ) : ℝ) * p)))) := by
    rw [phi_pos_formula havg, hlogarg]
    have hcancel : (n : ℝ) *
        ((((n - i : ℕ) : ℝ) * p) / (n : ℝ)) =
        ((n - i : ℕ) : ℝ) * p := by
      field_simp [hn0]
    calc
      (n : ℝ) * (2 * ((((n - i : ℕ) : ℝ) * p) / (n : ℝ)) *
          (1 + Real.log (2 * (n : ℝ) / (((n - i : ℕ) : ℝ) * p)))) =
          2 * ((n : ℝ) * ((((n - i : ℕ) : ℝ) * p) / (n : ℝ))) *
            (1 + Real.log (2 * (n : ℝ) / (((n - i : ℕ) : ℝ) * p))) := by ring
      _ = _ := by rw [hcancel]; ring
  rw [hrewrite] at hfull
  exact le_of_mul_le_mul_left hfull hiR

/-! ## Explicit finite uniform space interface -/

/-- The uniform mean on a nonempty finite sample space. -/
noncomputable def uniformExpect {Ω : Type*} [Fintype Ω]
    (X : Ω → ℝ) : ℝ :=
  (∑ ω : Ω, X ω) / (Fintype.card Ω : ℝ)

/-- Uniform event probability, using indicator sums. -/
noncomputable def uniformProb {Ω : Type*} [Fintype Ω]
    (E : Ω → Prop) : ℝ := by
  classical
  exact (∑ ω : Ω, if E ω then (1 : ℝ) else 0) /
    (Fintype.card Ω : ℝ)

theorem uniformProb_nonneg {Ω : Type*} [Fintype Ω]
    (E : Ω → Prop) : 0 ≤ uniformProb E := by
  classical
  unfold uniformProb
  apply div_nonneg
  · apply Finset.sum_nonneg
    intro ω hω
    split_ifs <;> norm_num
  · exact Nat.cast_nonneg _

open Classical in
/-- This theorem does not yet derive `htrunc` from the distributional tail
    estimate; `htrunc` is a P7 proof obligation. -/
theorem finiteUniform_aggregation
    {Ω : Type*} [Fintype Ω] [Nonempty Ω]
    {n i : ℕ} (hi : i < n)
    (U : Fin n → Ω → ℝ) (E : Fin n → Ω → Prop)
    (p V : ℝ) (hp : 0 < p)
    (hcount : (∑ r : Fin n, uniformProb (E r)) =
      ((n - i : ℕ) : ℝ) * p)
    (htrunc : ∀ r, uniformExpect
      (fun ω => if E r ω then U r ω else 0) ≤ phi (uniformProb (E r)))
    (hgreedy : ((n - i : ℕ) : ℝ) * V ≤
      ∑ r : Fin n, uniformExpect
        (fun ω => if E r ω then U r ω else 0)) :
    V ≤ 2 * p * (1 + Real.log (2 * (n : ℝ) /
      (((n - i : ℕ) : ℝ) * p))) := by
  exact tailAggregation_of_truncated hi
    (fun r => uniformProb (E r))
    (fun r => uniformExpect (fun ω => if E r ω then U r ω else 0))
    p V (fun r => uniformProb_nonneg (E r)) hp hcount htrunc hgreedy

end P7
