import P7_TailAggregation

/-!
# Tail bound to truncated expectation (the `htrunc` step of Lemma 4.3)

Let `Ω` be a nonempty finite set with `N` points, `U ≥ 0` and `E ⊆ Ω` with
`q = |E|/N`.  If `|{U > z}| ≤ 2 e^{-z/2} N` for every `z > 0`, then
`∑_{ω ∈ E} U ω ≤ N φ(q)` with `φ(q) = 2q(1 + ln(2/q))`, `φ(0) = 0`.

Proof: `U 1_E ≤ z₀ 1_E + (U - z₀)⁺`; the layer-cake formula (for the
counting measure) and the tail bound give `∑ (U - z₀)⁺ ≤ 4 N e^{-z₀/2}`;
take `z₀ = 2 ln (2/q)`.  This is the article's split of the integral at
`z = 2 ln(2/q)`.
-/

noncomputable section

namespace GradientKey.Truncation

open MeasureTheory Set Finset

variable {Ω : Type*} [Fintype Ω]

/-- Layer cake for a finite sum: `∑ f = ∫_{t>0} |{f > t}| dt` for `f ≥ 0`. -/
theorem sum_eq_integral_card_gt (f : Ω → ℝ) (hf : ∀ ω, 0 ≤ f ω) :
    (∑ ω, f ω) =
      ∫ t in Ioi (0 : ℝ),
        ((Finset.univ.filter (fun ω => t < f ω)).card : ℝ) := by
  classical
  letI : MeasurableSpace Ω := ⊤
  have hint : Integrable f (Measure.count : Measure Ω) := Integrable.of_finite
  have hnn : 0 ≤ᵐ[(Measure.count : Measure Ω)] f := Filter.Eventually.of_forall hf
  have h := hint.integral_eq_integral_meas_lt hnn
  rw [integral_count] at h
  rw [h]
  congr 1
  funext t
  have hset : {a : Ω | t < f a} = ↑(Finset.univ.filter (fun ω => t < f ω)) := by
    ext a; simp
  rw [hset, measureReal_def, Measure.count_apply_finset]
  simp

/-- From the tail bound to the bound on the excess over a threshold. -/
theorem sum_excess_le (U : Ω → ℝ) (N z₀ : ℝ) (hz₀ : 0 ≤ z₀)
    (htail : ∀ z : ℝ, 0 < z →
      ((Finset.univ.filter (fun ω => z < U ω)).card : ℝ) ≤
        2 * Real.exp (-z / 2) * N) :
    (∑ ω, max (U ω - z₀) 0) ≤ 4 * Real.exp (-z₀ / 2) * N := by
  classical
  rw [sum_eq_integral_card_gt (fun ω => max (U ω - z₀) 0) (fun ω => le_max_right _ _)]
  set C : ℝ := 2 * Real.exp (-z₀ / 2) * N
  have hC : 0 ≤ C := by
    have hN : 0 ≤ N := by
      have h1 := htail 1 one_pos
      have h0 : (0 : ℝ) ≤ ((Finset.univ.filter (fun ω => 1 < U ω)).card : ℝ) :=
        Nat.cast_nonneg _
      have hpos : 0 < 2 * Real.exp (-1 / 2) := by positivity
      by_contra hneg
      push Not at hneg
      have : 2 * Real.exp (-1 / 2) * N < 0 := mul_neg_of_pos_of_neg hpos hneg
      linarith
    positivity
  have hg : IntegrableOn (fun t : ℝ => C * Real.exp ((-1 / 2) * t)) (Ioi 0) :=
    (integrableOn_exp_mul_Ioi (by norm_num : (-1 / 2 : ℝ) < 0) 0).const_mul C
  have hmono :
      (∫ t in Ioi (0 : ℝ),
        ((Finset.univ.filter (fun ω => t < max (U ω - z₀) 0)).card : ℝ)) ≤
      ∫ t in Ioi (0 : ℝ), C * Real.exp ((-1 / 2) * t) := by
    apply integral_mono_of_nonneg
    · exact Filter.Eventually.of_forall (fun t => Nat.cast_nonneg _)
    · exact hg
    · apply ae_restrict_of_forall_mem measurableSet_Ioi
      intro t ht
      have ht : 0 < t := ht
      have hfilter : (Finset.univ.filter (fun ω => t < max (U ω - z₀) 0)) =
          Finset.univ.filter (fun ω => z₀ + t < U ω) := by
        apply Finset.filter_congr
        intro ω _
        constructor
        · intro h
          rcases le_total (U ω - z₀) 0 with h0 | h0
          · rw [max_eq_right h0] at h; linarith
          · rw [max_eq_left h0] at h; linarith
        · intro h
          rw [max_eq_left (by linarith)]
          linarith
      show ((Finset.univ.filter (fun ω => t < max (U ω - z₀) 0)).card : ℝ) ≤
        C * Real.exp ((-1 / 2) * t)
      rw [hfilter]
      have hb := htail (z₀ + t) (by linarith)
      calc ((Finset.univ.filter (fun ω => z₀ + t < U ω)).card : ℝ)
          ≤ 2 * Real.exp (-(z₀ + t) / 2) * N := hb
        _ = C * Real.exp ((-1 / 2) * t) := by
          simp only [C]
          rw [show -(z₀ + t) / 2 = -z₀ / 2 + (-1 / 2) * t by ring, Real.exp_add]
          ring
  refine hmono.trans (le_of_eq ?_)
  rw [integral_const_mul, integral_exp_mul_Ioi (by norm_num : (-1 / 2 : ℝ) < 0) 0]
  simp only [C, mul_zero, Real.exp_zero]
  ring

/-- The truncation lemma of Lemma 4.3, in counting form.
`E` is given as a finset of sample points. -/
theorem sum_on_event_le_phi [Nonempty Ω] (U : Ω → ℝ) (hU : ∀ ω, 0 ≤ U ω)
    (E : Finset Ω)
    (htail : ∀ z : ℝ, 0 < z →
      ((Finset.univ.filter (fun ω => z < U ω)).card : ℝ) ≤
        2 * Real.exp (-z / 2) * (Fintype.card Ω : ℝ)) :
    (∑ ω ∈ E, U ω) ≤
      (Fintype.card Ω : ℝ) * P7.phi ((E.card : ℝ) / (Fintype.card Ω : ℝ)) := by
  classical
  set N : ℝ := (Fintype.card Ω : ℝ)
  have hN : 0 < N := by simp only [N]; exact_mod_cast Fintype.card_pos
  by_cases hE : E.card = 0
  · rw [Finset.card_eq_zero.mp hE]
    simp
  set q : ℝ := (E.card : ℝ) / N
  have hq0 : 0 < q := by
    have : (0 : ℝ) < E.card := by exact_mod_cast Nat.pos_of_ne_zero hE
    positivity
  have hq1 : q ≤ 1 := by
    have : (E.card : ℝ) ≤ N := by simp only [N]; exact_mod_cast Finset.card_le_univ E
    exact (div_le_one hN).2 this
  set z₀ : ℝ := 2 * Real.log (2 / q)
  have hz₀ : 0 ≤ z₀ := by
    have : 1 ≤ 2 / q := by rw [le_div_iff₀ hq0]; linarith
    have := Real.log_nonneg this
    positivity
  have hpoint : ∀ ω, (if ω ∈ E then U ω else 0) ≤
      (if ω ∈ E then z₀ else 0) + max (U ω - z₀) 0 := by
    intro ω
    split_ifs
    · have := le_max_left (U ω - z₀) 0
      linarith
    · simp
  have hsum : (∑ ω ∈ E, U ω) ≤ z₀ * E.card + ∑ ω, max (U ω - z₀) 0 := by
    have h1 : (∑ ω ∈ E, U ω) = ∑ ω, (if ω ∈ E then U ω else 0) := by
      rw [Finset.sum_ite_mem, Finset.univ_inter]
    have h2 : (∑ ω, (if ω ∈ E then z₀ else (0 : ℝ))) = z₀ * E.card := by
      rw [Finset.sum_ite_mem, Finset.univ_inter, Finset.sum_const, nsmul_eq_mul]
      ring
    rw [h1, ← h2, ← Finset.sum_add_distrib]
    exact Finset.sum_le_sum (fun ω _ => hpoint ω)
  have hexc := sum_excess_le U N z₀ hz₀ htail
  have hexp : Real.exp (-z₀ / 2) = q / 2 := by
    have : -z₀ / 2 = -Real.log (2 / q) := by
      simp only [z₀]; ring
    rw [this, Real.exp_neg, Real.exp_log (by positivity), inv_div]
  have hcard : (E.card : ℝ) = q * N := by
    simp only [q]; field_simp
  rw [P7.phi_pos_formula hq0]
  calc (∑ ω ∈ E, U ω) ≤ z₀ * E.card + ∑ ω, max (U ω - z₀) 0 := hsum
    _ ≤ z₀ * E.card + 4 * Real.exp (-z₀ / 2) * N := by linarith
    _ = N * (2 * q * (1 + Real.log (2 / q))) := by
      rw [hexp, hcard]
      simp only [z₀]
      ring

end GradientKey.Truncation
