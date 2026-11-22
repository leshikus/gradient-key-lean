import Mathlib

/-!
# Gradient key: Section 4, Theorem 4.4

This formalizes the summation argument in Theorem 4.4 and its three
consequences, parametrized by the estimates proved in Lemmas 4.1--4.3.

The file includes a finite uniform table-column model, a concrete greedy
candidate-set recursion, the finite-average algebra and the conditional
row-deletion mean estimate of Lemma 4.2 (in terms of valid extensions).
Theorem 4.4 and its corollaries are still conditional on the path-size
transition and the bounds of Lemma 4.3.  The one-row mean estimate and the
finite averaging argument needed for Lemma 4.3 are developed below, but
the bridges to the concrete greedy tree and the Hoeffding tail bound remain.
The logarithmic chord inequality is proved, not assumed.

This file has not been compiler-checked: Lean and Mathlib are not installed
in this environment. There are no `sorry` or `axiom` declarations; this does
NOT imply that it compiles or constitutes a complete formal proof.
-/

noncomputable section

namespace GradientKey

open Finset

/-- The weight `2^(i-h)` occurring in the article, with natural indices. -/
private def weight (h i : ℕ) : ℝ := (2 : ℝ) ^ i / (2 : ℝ) ^ h

private lemma weight_nonneg (h i : ℕ) : 0 ≤ weight h i := by
  unfold weight
  positivity

private lemma weight_le_one (h i : ℕ) (hi : i ≤ h) :
    weight h i ≤ 1 := by
  unfold weight
  apply (div_le_one (by positivity : (0 : ℝ) < (2 : ℝ) ^ h)).2
  exact pow_le_pow_right₀ (by norm_num : (1 : ℝ) ≤ 2) hi

private lemma weight_succ (h i : ℕ) :
    weight (h + 1) i = weight h i / 2 := by
  unfold weight
  rw [pow_succ]
  have hp : (2 : ℝ) ^ h ≠ 0 := by positivity
  field_simp <;> ring

private lemma weight_diag_succ (h : ℕ) :
    weight (h + 1) h = (1 : ℝ) / 2 := by
  unfold weight
  rw [pow_succ]
  have hp : (2 : ℝ) ^ h ≠ 0 := by positivity
  field_simp <;> ring

private lemma sum_powers_two (h : ℕ) :
    (∑ i ∈ Finset.range h, (2 : ℝ) ^ i) = (2 : ℝ) ^ h - 1 := by
  induction h with
  | zero => norm_num
  | succ h ih =>
      rw [Finset.sum_range_succ, ih, pow_succ]
      ring

private lemma sum_weights (h : ℕ) :
    (∑ i ∈ Finset.range h, weight h i) = 1 - 1 / (2 : ℝ) ^ h := by
  simp only [weight, ← Finset.sum_div]
  rw [sum_powers_two]
  have hp : (2 : ℝ) ^ h ≠ 0 := by positivity
  field_simp <;> ring

private lemma sum_one_sub_weights (h : ℕ) :
    (∑ i ∈ Finset.range h, (1 - weight h i)) =
      (h : ℝ) - 1 + 1 / (2 : ℝ) ^ h := by
  calc
    (∑ i ∈ Finset.range h, (1 - weight h i)) =
        (h : ℝ) - ∑ i ∈ Finset.range h, weight h i := by
          rw [Finset.sum_sub_distrib]
          simp
    _ = (h : ℝ) - 1 + 1 / (2 : ℝ) ^ h := by
          rw [sum_weights]
          ring

/-!
## A deterministic identity behind Lemma 4.1

At a fork of size `s = a + b`, uniform choice of a leaf gives expected
next candidate-set size `(a²+b²)/s`. This calculation is algebraic and
requires no probabilistic assumptions.
-/

private lemma split_size_identity (a b : ℝ) (hs : 0 < a + b) :
    (a * a + b * b) / (a + b) - 1 =
      ((a + b - 1) - 1 + (a - b) ^ 2 / (a + b)) / 2 := by
  have hs0 : a + b ≠ 0 := ne_of_gt hs
  field_simp <;> ring

/-- The exact summation in Theorem 4.4 from the recurrence (Lemma 4.1)
and a pointwise bound `b i` for the expected imbalance (Lemma 4.3).
There is no probability-theory axiom hidden in this theorem. -/
theorem uniform_bound_from_lemmas
    (m ell : ℕ) (t : ℝ) (e p V b : ℕ → ℝ)
    (hInit : e 0 = (m : ℝ) - 1)
    (hRec : ∀ i, e (i + 1) = (e i - p i + V i) / 2)
    (hTail : ∀ h, t ≤ (∑ i ∈ Finset.range h, p i) + e h)
    (hProb : ∀ i, p i ≤ 1)
    (hV : ∀ i < ell, V i ≤ b i) :
    t ≤ (ell : ℝ) - 1 + (m : ℝ) / (2 : ℝ) ^ ell +
      ∑ i ∈ Finset.range ell, weight ell i * b i := by
  have hE : ∀ h, e h =
      ((m : ℝ) - 1) / (2 : ℝ) ^ h +
        ∑ i ∈ Finset.range h, weight h i * (V i - p i) := by
    intro h
    induction h with
    | zero => simp [hInit, weight]
    | succ h ih =>
        have hShift :
            (∑ i ∈ Finset.range h, weight h i * (V i - p i)) / 2 =
              ∑ i ∈ Finset.range h, weight (h + 1) i * (V i - p i) := by
          rw [Finset.sum_div]
          apply Finset.sum_congr rfl
          intro i hi
          rw [weight_succ]
          ring
        rw [hRec h, ih, Finset.sum_range_succ]
        rw [weight_diag_succ, ← hShift, pow_succ]
        have hp : (2 : ℝ) ^ h ≠ 0 := by positivity
        field_simp <;> ring
  have hSum :
      (∑ i ∈ Finset.range ell, p i) +
        (∑ i ∈ Finset.range ell, weight ell i * (V i - p i)) =
      (∑ i ∈ Finset.range ell, (1 - weight ell i) * p i) +
        (∑ i ∈ Finset.range ell, weight ell i * V i) := by
    rw [← Finset.sum_add_distrib, ← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro i hi
    ring
  have hFirst : t ≤
      ((m : ℝ) - 1) / (2 : ℝ) ^ ell +
        (∑ i ∈ Finset.range ell, (1 - weight ell i) * p i) +
        (∑ i ∈ Finset.range ell, weight ell i * V i) := by
    calc
      t ≤ (∑ i ∈ Finset.range ell, p i) + e ell := hTail ell
      _ = ((m : ℝ) - 1) / (2 : ℝ) ^ ell +
          ((∑ i ∈ Finset.range ell, p i) +
           (∑ i ∈ Finset.range ell, weight ell i * (V i - p i))) := by
             rw [hE ell]
             ring
      _ = ((m : ℝ) - 1) / (2 : ℝ) ^ ell +
          ((∑ i ∈ Finset.range ell, (1 - weight ell i) * p i) +
           (∑ i ∈ Finset.range ell, weight ell i * V i)) := by
             rw [hSum]
      _ = _ := by ring
  have hCoeff :
      (∑ i ∈ Finset.range ell, (1 - weight ell i) * p i) ≤
        ∑ i ∈ Finset.range ell, (1 - weight ell i) := by
    apply Finset.sum_le_sum
    intro i hi
    calc
      (1 - weight ell i) * p i ≤ (1 - weight ell i) * 1 :=
        mul_le_mul_of_nonneg_left (hProb i)
          (sub_nonneg.mpr (weight_le_one ell i
            (Nat.le_of_lt (Finset.mem_range.mp hi))))
      _ = 1 - weight ell i := by ring
  have hMain : t ≤ (ell : ℝ) - 1 + (m : ℝ) / (2 : ℝ) ^ ell +
      ∑ i ∈ Finset.range ell, weight ell i * V i := by
    calc
      t ≤ ((m : ℝ) - 1) / (2 : ℝ) ^ ell +
          (∑ i ∈ Finset.range ell, (1 - weight ell i) * p i) +
          (∑ i ∈ Finset.range ell, weight ell i * V i) := hFirst
      _ ≤ ((m : ℝ) - 1) / (2 : ℝ) ^ ell +
          (∑ i ∈ Finset.range ell, (1 - weight ell i)) +
          (∑ i ∈ Finset.range ell, weight ell i * V i) := by
            linarith only [hCoeff]
      _ = (ell : ℝ) - 1 + (m : ℝ) / (2 : ℝ) ^ ell +
          ∑ i ∈ Finset.range ell, weight ell i * V i := by
            rw [sum_one_sub_weights]
            ring
  have hLast :
      (∑ i ∈ Finset.range ell, weight ell i * V i) ≤
        ∑ i ∈ Finset.range ell, weight ell i * b i := by
    apply Finset.sum_le_sum
    intro i hi
    exact mul_le_mul_of_nonneg_left
      (hV i (Finset.mem_range.mp hi)) (weight_nonneg ell i)
  linarith only [hMain, hLast]

/-- The specific upper bound displayed in Theorem 4.4. -/
def imbalanceBound (n i : ℕ) : ℝ :=
  min ((n : ℝ) / ((n : ℝ) - (i : ℝ)))
      (2 + 2 * Real.log (2 * (n : ℝ) / ((n : ℝ) - (i : ℝ))))

theorem theorem_4_4_main
    (n m ell : ℕ) (t : ℝ) (e p V : ℕ → ℝ)
    (hInit : e 0 = (m : ℝ) - 1)
    (hRec : ∀ i, e (i + 1) = (e i - p i + V i) / 2)
    (hTail : ∀ h, t ≤ (∑ i ∈ Finset.range h, p i) + e h)
    (hProb : ∀ i, p i ≤ 1)
    (hV : ∀ i < ell, V i ≤ imbalanceBound n i) :
    t ≤ (ell : ℝ) - 1 + (m : ℝ) / (2 : ℝ) ^ ell +
      ∑ i ∈ Finset.range ell, weight ell i * imbalanceBound n i := by
  exact uniform_bound_from_lemmas m ell t e p V (imbalanceBound n)
    hInit hRec hTail hProb hV

/-- Strictness of the corollaries comes from `sum_i 2^(i-ell) < 1`.
The logarithmic chord inequality is proved below, and supplied here. -/
private theorem strict_bound_of_pointwise
    (m ell : ℕ) (t limit C : ℝ) (b : ℕ → ℝ)
    (hEll : 0 < ell)
    (hBound : t ≤ (ell : ℝ) - 1 + (m : ℝ) / (2 : ℝ) ^ ell +
      ∑ i ∈ Finset.range ell, weight ell i * b i)
    (hChord : (ell : ℝ) - 1 + (m : ℝ) / (2 : ℝ) ^ ell ≤ limit)
    (hC : 0 < C)
    (hb : ∀ i < ell, b i ≤ C) : t < limit + C := by
  have hSum :
      (∑ i ∈ Finset.range ell, weight ell i * b i) ≤
        C * (∑ i ∈ Finset.range ell, weight ell i) := by
    calc
      (∑ i ∈ Finset.range ell, weight ell i * b i) ≤
          ∑ i ∈ Finset.range ell, weight ell i * C := by
            apply Finset.sum_le_sum
            intro i hi
            exact mul_le_mul_of_nonneg_left
              (hb i (Finset.mem_range.mp hi)) (weight_nonneg ell i)
      _ = C * (∑ i ∈ Finset.range ell, weight ell i) := by
            rw [← Finset.sum_mul]
            ring
  have hWlt : (∑ i ∈ Finset.range ell, weight ell i) < 1 := by
    rw [sum_weights]
    have hp : 0 < (1 : ℝ) / (2 : ℝ) ^ ell := by positivity
    linarith
  have hStrict : C * (∑ i ∈ Finset.range ell, weight ell i) < C := by
    calc
      C * (∑ i ∈ Finset.range ell, weight ell i) < C * 1 :=
        mul_lt_mul_of_pos_left hWlt hC
      _ = C := by ring
  linarith only [hBound, hChord, hSum, hStrict]

private lemma ratio_le_ell (n ell i : ℕ) (hi : i < ell)
    (hLe : ell ≤ n) :
    (n : ℝ) / ((n : ℝ) - (i : ℝ)) ≤ (ell : ℝ) := by
  have hi' : (i : ℝ) + 1 ≤ (ell : ℝ) := by
    exact_mod_cast (Nat.succ_le_iff.mpr hi)
  have hLe' : (ell : ℝ) ≤ (n : ℝ) := by exact_mod_cast hLe
  have hiNonneg : 0 ≤ (i : ℝ) := Nat.cast_nonneg _
  have hd : 0 < (n : ℝ) - (i : ℝ) := by linarith
  have hp : 0 ≤ (i : ℝ) * ((n : ℝ) - (i : ℝ) - 1) :=
    mul_nonneg hiNonneg (by linarith)
  have h1 : (n : ℝ) ≤ ((i : ℝ) + 1) * ((n : ℝ) - (i : ℝ)) := by
    nlinarith only [hp]
  have h2 : ((i : ℝ) + 1) * ((n : ℝ) - (i : ℝ)) ≤
      (ell : ℝ) * ((n : ℝ) - (i : ℝ)) :=
    mul_le_mul_of_nonneg_right hi' (le_of_lt hd)
  exact (div_le_iff₀ hd).2 (h1.trans h2)

private lemma ratio_le_coarse (n ell i : ℕ) (hi : i < ell)
    (hLe : ell ≤ n) :
    (n : ℝ) / ((n : ℝ) - (i : ℝ)) ≤
      1 + ((ell : ℝ) - 1) / ((n : ℝ) - (ell : ℝ) + 1) := by
  have hi' : (i : ℝ) + 1 ≤ (ell : ℝ) := by
    exact_mod_cast (Nat.succ_le_iff.mpr hi)
  have hLe' : (ell : ℝ) ≤ (n : ℝ) := by exact_mod_cast hLe
  have hD : 0 < (n : ℝ) - (ell : ℝ) + 1 := by linarith
  have hd : 0 < (n : ℝ) - (i : ℝ) := by linarith
  have hDen : (n : ℝ) - (ell : ℝ) + 1 ≤ (n : ℝ) - (i : ℝ) :=
    by linarith
  have hn : 0 ≤ (n : ℝ) := Nat.cast_nonneg _
  have h1 : (n : ℝ) / ((n : ℝ) - (i : ℝ)) ≤
      (n : ℝ) / ((n : ℝ) - (ell : ℝ) + 1) := by
    apply (div_le_div_iff₀ hd hD).2
    exact mul_le_mul_of_nonneg_left hDen hn
  have h2 : (n : ℝ) / ((n : ℝ) - (ell : ℝ) + 1) =
      1 + ((ell : ℝ) - 1) / ((n : ℝ) - (ell : ℝ) + 1) := by
    have hne : (n : ℝ) - (ell : ℝ) + 1 ≠ 0 := ne_of_gt hD
    field_simp <;> ring
  calc
    (n : ℝ) / ((n : ℝ) - (i : ℝ)) ≤
        (n : ℝ) / ((n : ℝ) - (ell : ℝ) + 1) := h1
    _ = _ := h2

private lemma imbalanceBound_le_log (n ell i : ℕ) (hi : i < ell)
    (hLe : ell ≤ n) :
    imbalanceBound n i ≤ 2 + 2 * Real.log (2 * (ell : ℝ)) := by
  have hr := ratio_le_ell n ell i hi hLe
  have hn' : (n : ℝ) - (i : ℝ) > 0 := by
    have hi' : (i : ℝ) + 1 ≤ (ell : ℝ) := by
      exact_mod_cast (Nat.succ_le_iff.mpr hi)
    have hLe' : (ell : ℝ) ≤ (n : ℝ) := by exact_mod_cast hLe
    linarith
  have hcpos : 0 < 2 * (n : ℝ) / ((n : ℝ) - (i : ℝ)) := by
    have hiNonneg : 0 ≤ (i : ℝ) := Nat.cast_nonneg _
    have hnpos : 0 < (n : ℝ) := by linarith
    positivity
  have hc : 2 * (n : ℝ) / ((n : ℝ) - (i : ℝ)) ≤
      2 * (ell : ℝ) := by
    calc
      2 * (n : ℝ) / ((n : ℝ) - (i : ℝ)) =
          2 * ((n : ℝ) / ((n : ℝ) - (i : ℝ))) := by ring
      _ ≤ 2 * (ell : ℝ) := by linarith
  have hl : Real.log (2 * (n : ℝ) / ((n : ℝ) - (i : ℝ))) ≤
      Real.log (2 * (ell : ℝ)) := Real.log_le_log hcpos hc
  unfold imbalanceBound
  exact (min_le_right _ _).trans (by linarith)

private lemma imbalanceBound_le_coarse (n ell i : ℕ) (hi : i < ell)
    (hLe : ell ≤ n) :
    imbalanceBound n i ≤
      1 + ((ell : ℝ) - 1) / ((n : ℝ) - (ell : ℝ) + 1) := by
  exact (min_le_left _ _).trans (ratio_le_coarse n ell i hi hLe)


/-!
## The logarithmic chord inequality

The paper uses `ell - 1 + m / 2^ell ≤ log₂ m`.  This is a consequence
of concavity of the natural logarithm on the interval [1, 2].
-/

/-- The logarithm lies above the chord between `(1, 0)` and `(2, 1)`. -/
private lemma logb_two_chord (x : ℝ) (hx1 : 1 ≤ x) (hx2 : x ≤ 2) :
    x - 1 ≤ Real.logb 2 x := by
  have hconc := strictConcaveOn_log_Ioi.concaveOn
  have hraw := hconc.2
    (show (1 : ℝ) ∈ Set.Ioi 0 by norm_num)
    (show (2 : ℝ) ∈ Set.Ioi 0 by norm_num)
    (show 0 ≤ (2 : ℝ) - x by linarith)
    (show 0 ≤ x - 1 by linarith)
    (show (2 : ℝ) - x + (x - 1) = 1 by ring)
  have hlog : (x - 1) * Real.log (2 : ℝ) ≤ Real.log x := by
    simp only [smul_eq_mul, Real.log_one, mul_zero, zero_add] at hraw
    have hx : (2 - x) * (1 : ℝ) + (x - 1) * 2 = x := by ring
    rw [hx] at hraw
    linarith only [hraw]
  have hlog2 : 0 < Real.log (2 : ℝ) := Real.log_pos (by norm_num)
  change x - 1 ≤ Real.log x / Real.log 2
  exact (le_div_iff₀ hlog2).2 hlog

/-- The exact chord inequality used in all three corollaries. -/
private lemma binary_window_chord (m ell : ℕ)
    (hlo : (2 : ℝ) ^ ell ≤ (m : ℝ))
    (hhi : (m : ℝ) ≤ 2 * (2 : ℝ) ^ ell) :
    (ell : ℝ) - 1 + (m : ℝ) / (2 : ℝ) ^ ell ≤
      Real.logb 2 (m : ℝ) := by
  let x : ℝ := (m : ℝ) / (2 : ℝ) ^ ell
  have hp : 0 < (2 : ℝ) ^ ell := by positivity
  have hx1 : 1 ≤ x := by
    change 1 ≤ (m : ℝ) / (2 : ℝ) ^ ell
    exact (le_div_iff₀ hp).2 (by simpa using hlo)
  have hx2 : x ≤ 2 := by
    change (m : ℝ) / (2 : ℝ) ^ ell ≤ 2
    exact (div_le_iff₀ hp).2 (by simpa [mul_comm] using hhi)
  have hx0 : x ≠ 0 := ne_of_gt (lt_of_lt_of_le (by norm_num) hx1)
  have hmul : (2 : ℝ) ^ ell * x = (m : ℝ) := by
    dsimp [x]
    have hp0 : (2 : ℝ) ^ ell ≠ 0 := ne_of_gt hp
    field_simp <;> ring
  have hlog : Real.logb 2 (m : ℝ) =
      (ell : ℝ) + Real.logb 2 x := by
    rw [← hmul, Real.logb_mul (ne_of_gt hp) hx0,
      Real.logb_pow, Real.logb_self_eq_one (by norm_num)]
    ring
  have hchord := logb_two_chord x hx1 hx2
  change (ell : ℝ) - 1 + x ≤ Real.logb 2 (m : ℝ)
  rw [hlog]
  linarith only [hchord]

/-- For `m ≥ 2`, floor logarithm provides the two powers-of-two bounds. -/
private lemma nat_log_binary_window (m : ℕ) (hm : 2 ≤ m) :
    (2 : ℝ) ^ (Nat.log 2 m) ≤ (m : ℝ) ∧
      (m : ℝ) ≤ 2 * (2 : ℝ) ^ (Nat.log 2 m) := by
  have hm0 : m ≠ 0 := by omega
  have hlo : 2 ^ Nat.log 2 m ≤ m := Nat.pow_log_le_self 2 hm0
  have hhi : m < 2 ^ (Nat.log 2 m + 1) :=
    Nat.lt_pow_succ_log_self (by norm_num) m
  constructor
  · exact_mod_cast hlo
  · have hh : (m : ℝ) ≤ (2 : ℝ) ^ (Nat.log 2 m + 1) := by
      exact_mod_cast (Nat.le_of_lt hhi)
    rw [pow_succ] at hh
    linarith

private lemma nat_log_pos_and_le (n m : ℕ) (hm : 2 ≤ m)
    (hsize : m ≤ 2 ^ n) :
    0 < Nat.log 2 m ∧ Nat.log 2 m ≤ n := by
  constructor
  · exact Nat.log_pos (by norm_num) hm
  · have h := Nat.log_mono_right (b := 2) hsize
    simpa only [Nat.log_pow (by norm_num : 1 < (2 : ℕ))] using h

/-!
## Passing from Lemma 4.3 to the displayed pointwise bound

Instead of appealing to monotonicity of `p ↦ p(1 + log(c/p))`, use
`log y ≤ y - 1` with `y = 1/p`.  This gives
`p(1 + log(c/p)) ≤ 1 + log c` for `0 < p ≤ 1 ≤ c`.
-/

private lemma entropy_log_bound (c p : ℝ)
    (hc : 1 ≤ c) (hp0 : 0 < p) (hp1 : p ≤ 1) :
    p * (1 + Real.log (c / p)) ≤ 1 + Real.log c := by
  have hc0 : 0 < c := lt_of_lt_of_le (by norm_num) hc
  have hlog : Real.log (1 / p) ≤ 1 / p - 1 :=
    Real.log_le_sub_one_of_pos (by positivity)
  have hlogeq : Real.log (c / p) =
      Real.log c + Real.log (1 / p) := by
    rw [Real.log_div (ne_of_gt hc0) (ne_of_gt hp0),
      Real.log_div (by norm_num : (1 : ℝ) ≠ 0) (ne_of_gt hp0)]
    simp [sub_eq_add_neg]
  have hmul : p * Real.log (1 / p) ≤ 1 - p := by
    have h := mul_le_mul_of_nonneg_left hlog hp0.le
    have hunit : p * (1 / p) = 1 := by
      field_simp
    nlinarith only [h, hunit]
  have hcLog : 0 ≤ Real.log c := Real.log_nonneg hc
  have hrest : 0 ≤ (1 - p) * Real.log c :=
    mul_nonneg (by linarith) hcLog
  rw [hlogeq]
  nlinarith only [hmul, hrest]

/-- Lemma 4.3 in its original form implies the bound on `V_i`
used in the displayed estimate of Theorem 4.4. -/
private lemma imbalance_of_lemma_4_3 (n i : ℕ) (hi : i < n)
    (p v : ℝ) (hp0 : 0 ≤ p) (hp1 : p ≤ 1)
    (hzero : p = 0 → v = 0)
    (hmean : v ≤ (n : ℝ) / ((n : ℝ) - (i : ℝ)))
    (htail : 0 < p →
      v ≤ 2 * p * (1 + Real.log
        (2 * (n : ℝ) / (((n : ℝ) - (i : ℝ)) * p)))) :
    v ≤ imbalanceBound n i := by
  have hi' : (i : ℝ) < (n : ℝ) := by exact_mod_cast hi
  have hn : 0 < (n : ℝ) - (i : ℝ) := by linarith
  have hc : 1 ≤ 2 * (n : ℝ) / ((n : ℝ) - (i : ℝ)) := by
    apply (le_div_iff₀ hn).2
    have hi0 : 0 ≤ (i : ℝ) := Nat.cast_nonneg _
    linarith
  let c := 2 * (n : ℝ) / ((n : ℝ) - (i : ℝ))
  have hlogc : 0 ≤ Real.log c := Real.log_nonneg hc
  unfold imbalanceBound
  apply le_min hmean
  by_cases hpos : 0 < p
  · have hid : 2 * (n : ℝ) / (((n : ℝ) - (i : ℝ)) * p) = c / p := by
      dsimp [c]
      have hpne : p ≠ 0 := ne_of_gt hpos
      have hdne : (n : ℝ) - (i : ℝ) ≠ 0 := ne_of_gt hn
      field_simp <;> ring
    have ht : v ≤ 2 * p * (1 + Real.log (c / p)) := by
      simpa only [hid] using htail hpos
    have he := entropy_log_bound c p hc hpos hp1
    change v ≤ 2 + 2 * Real.log c
    linarith only [ht, he]
  · have hpz : p = 0 := le_antisymm (le_of_not_gt hpos) hp0
    change v ≤ 2 + 2 * Real.log c
    rw [hzero hpz]
    linarith only [hlogc]


/-- Part (a) of Theorem 4.4, given Lemmas 4.1--4.3 and the
logarithmic chord inequality, now proved from the floor-log window. -/
theorem theorem_4_4_a
    (n m ell : ℕ) (t : ℝ) (e p V : ℕ → ℝ)
    (hInit : e 0 = (m : ℝ) - 1)
    (hRec : ∀ i, e (i + 1) = (e i - p i + V i) / 2)
    (hTail : ∀ h, t ≤ (∑ i ∈ Finset.range h, p i) + e h)
    (hProb : ∀ i, p i ≤ 1)
    (hV : ∀ i < ell, V i ≤ imbalanceBound n i)
    (hEll : 0 < ell) (hLe : ell ≤ n)
    (hlo : (2 : ℝ) ^ ell ≤ (m : ℝ))
    (hhi : (m : ℝ) ≤ 2 * (2 : ℝ) ^ ell) :
    t < Real.logb 2 (m : ℝ) + 2 + 2 * Real.log (2 * (ell : ℝ)) := by
  have hC : 0 < 2 + 2 * Real.log (2 * (ell : ℝ)) := by
    have hEll' : (1 : ℝ) ≤ (ell : ℝ) := by
      exact_mod_cast (Nat.succ_le_iff.mpr hEll)
    have hlog : 0 ≤ Real.log (2 * (ell : ℝ)) :=
      Real.log_nonneg (by linarith)
    linarith
  have hb := theorem_4_4_main n m ell t e p V
    hInit hRec hTail hProb hV
  have hChord := binary_window_chord m ell hlo hhi
  have hs := strict_bound_of_pointwise m ell t
    (Real.logb 2 (m : ℝ)) (2 + 2 * Real.log (2 * (ell : ℝ)))
    (imbalanceBound n) hEll hb hChord hC
    (fun i hi => imbalanceBound_le_log n ell i hi hLe)
  linarith only [hs]

/-- Part (b) of Theorem 4.4. -/
theorem theorem_4_4_b
    (n m ell : ℕ) (t : ℝ) (e p V : ℕ → ℝ)
    (hInit : e 0 = (m : ℝ) - 1)
    (hRec : ∀ i, e (i + 1) = (e i - p i + V i) / 2)
    (hTail : ∀ h, t ≤ (∑ i ∈ Finset.range h, p i) + e h)
    (hProb : ∀ i, p i ≤ 1)
    (hV : ∀ i < ell, V i ≤ imbalanceBound n i)
    (hEll : 0 < ell) (hLe : ell ≤ n)
    (hlo : (2 : ℝ) ^ ell ≤ (m : ℝ))
    (hhi : (m : ℝ) ≤ 2 * (2 : ℝ) ^ ell) :
    t < Real.logb 2 (m : ℝ) + 1 +
      ((ell : ℝ) - 1) / ((n : ℝ) - (ell : ℝ) + 1) := by
  have hEll' : (1 : ℝ) ≤ (ell : ℝ) := by
      exact_mod_cast (Nat.succ_le_iff.mpr hEll)
  have hLe' : (ell : ℝ) ≤ (n : ℝ) := by exact_mod_cast hLe
  have hD : 0 < (n : ℝ) - (ell : ℝ) + 1 := by linarith
  have hC : 0 < 1 + ((ell : ℝ) - 1) /
      ((n : ℝ) - (ell : ℝ) + 1) := by
    have hnonneg : 0 ≤ ((ell : ℝ) - 1) /
        ((n : ℝ) - (ell : ℝ) + 1) :=
      div_nonneg (by linarith) (le_of_lt hD)
    linarith
  have hb := theorem_4_4_main n m ell t e p V
    hInit hRec hTail hProb hV
  have hChord := binary_window_chord m ell hlo hhi
  have hs := strict_bound_of_pointwise m ell t
    (Real.logb 2 (m : ℝ))
    (1 + ((ell : ℝ) - 1) / ((n : ℝ) - (ell : ℝ) + 1))
    (imbalanceBound n) hEll hb hChord hC
    (fun i hi => imbalanceBound_le_coarse n ell i hi hLe)
  linarith only [hs]

/-- Part (c) of Theorem 4.4. -/
theorem theorem_4_4_c
    (n m ell : ℕ) (t : ℝ) (e p V : ℕ → ℝ)
    (hInit : e 0 = (m : ℝ) - 1)
    (hRec : ∀ i, e (i + 1) = (e i - p i + V i) / 2)
    (hTail : ∀ h, t ≤ (∑ i ∈ Finset.range h, p i) + e h)
    (hProb : ∀ i, p i ≤ 1)
    (hV : ∀ i < ell, V i ≤ imbalanceBound n i)
    (hEll : 0 < ell) (hLe : ell ≤ n)
    (hlo : (2 : ℝ) ^ ell ≤ (m : ℝ))
    (hhi : (m : ℝ) ≤ 2 * (2 : ℝ) ^ ell)
    (hSize : n ≥ 2 * ell - 2) :
    t < Real.logb 2 (m : ℝ) + 2 := by
  have hb := theorem_4_4_b n m ell t e p V
    hInit hRec hTail hProb hV hEll hLe hlo hhi
  have hLe' : (ell : ℝ) ≤ (n : ℝ) := by exact_mod_cast hLe
  have hEll' : (1 : ℝ) ≤ (ell : ℝ) := by
      exact_mod_cast (Nat.succ_le_iff.mpr hEll)
  have hD : 0 < (n : ℝ) - (ell : ℝ) + 1 := by linarith
  have hSizeNat : 2 * ell ≤ n + 2 := by omega
  have hSize' : (2 : ℝ) * (ell : ℝ) ≤ (n : ℝ) + 2 := by
    exact_mod_cast hSizeNat
  have hFraction : ((ell : ℝ) - 1) /
      ((n : ℝ) - (ell : ℝ) + 1) ≤ 1 := by
    apply (div_le_one hD).2
    linarith
  linarith only [hb, hFraction]

/-!
## Corollaries with `ell = Nat.log 2 m`

These statements have no free logarithmic chord hypothesis and use the original
range `2 ≤ m ≤ 2^n`. The only non-arithmetic obligations are Lemmas 4.1--4.3.
-/

/-- Theorem 4.4(a), taking `ell` to be `floor(log₂ m)`. -/
theorem theorem_4_4_a_nat (n m : ℕ)
    (t : ℝ) (e p V : ℕ → ℝ)
    (hm : 2 ≤ m) (hsize : m ≤ 2 ^ n)
    (hInit : e 0 = (m : ℝ) - 1)
    (hRec : ∀ i, e (i + 1) = (e i - p i + V i) / 2)
    (hTail : ∀ h, t ≤ (∑ i ∈ Finset.range h, p i) + e h)
    (hProb : ∀ i, p i ≤ 1)
    (hV : ∀ i < Nat.log 2 m, V i ≤ imbalanceBound n i) :
    t < Real.logb 2 (m : ℝ) + 2 +
      2 * Real.log (2 * (Nat.log 2 m : ℝ)) := by
  obtain ⟨hpos, hle⟩ := nat_log_pos_and_le n m hm hsize
  obtain ⟨hlo, hhi⟩ := nat_log_binary_window m hm
  exact theorem_4_4_a n m (Nat.log 2 m) t e p V
    hInit hRec hTail hProb hV hpos hle hlo hhi

/-- Theorem 4.4(b), with its integer logarithm fixed by Mathlib. -/
theorem theorem_4_4_b_nat (n m : ℕ)
    (t : ℝ) (e p V : ℕ → ℝ)
    (hm : 2 ≤ m) (hsize : m ≤ 2 ^ n)
    (hInit : e 0 = (m : ℝ) - 1)
    (hRec : ∀ i, e (i + 1) = (e i - p i + V i) / 2)
    (hTail : ∀ h, t ≤ (∑ i ∈ Finset.range h, p i) + e h)
    (hProb : ∀ i, p i ≤ 1)
    (hV : ∀ i < Nat.log 2 m, V i ≤ imbalanceBound n i) :
    t < Real.logb 2 (m : ℝ) + 1 +
      ((Nat.log 2 m : ℝ) - 1) /
      ((n : ℝ) - (Nat.log 2 m : ℝ) + 1) := by
  obtain ⟨hpos, hle⟩ := nat_log_pos_and_le n m hm hsize
  obtain ⟨hlo, hhi⟩ := nat_log_binary_window m hm
  exact theorem_4_4_b n m (Nat.log 2 m) t e p V
    hInit hRec hTail hProb hV hpos hle hlo hhi

/-- Theorem 4.4(c), with the size assumption on the row count. -/
theorem theorem_4_4_c_nat (n m : ℕ)
    (t : ℝ) (e p V : ℕ → ℝ)
    (hm : 2 ≤ m) (hsize : m ≤ 2 ^ n)
    (hInit : e 0 = (m : ℝ) - 1)
    (hRec : ∀ i, e (i + 1) = (e i - p i + V i) / 2)
    (hTail : ∀ h, t ≤ (∑ i ∈ Finset.range h, p i) + e h)
    (hProb : ∀ i, p i ≤ 1)
    (hV : ∀ i < Nat.log 2 m, V i ≤ imbalanceBound n i)
    (hn : 2 * Nat.log 2 m - 2 ≤ n) :
    t < Real.logb 2 (m : ℝ) + 2 := by
  obtain ⟨hpos, hle⟩ := nat_log_pos_and_le n m hm hsize
  obtain ⟨hlo, hhi⟩ := nat_log_binary_window m hm
  exact theorem_4_4_c n m (Nat.log 2 m) t e p V
    hInit hRec hTail hProb hV hpos hle hlo hhi hn

/-- The explicit main inequality, starting with precisely the two Lemma 4.3
estimates rather than a pre-combined `V_i` bound. -/
theorem theorem_4_4_from_lemmas_4_1_and_4_3 (n m : ℕ)
    (t : ℝ) (e p V : ℕ → ℝ)
    (hm : 2 ≤ m) (hsize : m ≤ 2 ^ n)
    (hInit : e 0 = (m : ℝ) - 1)
    (hRec : ∀ i, e (i + 1) = (e i - p i + V i) / 2)
    (hTail : ∀ h, t ≤ (∑ i ∈ Finset.range h, p i) + e h)
    (hProbNonneg : ∀ i, 0 ≤ p i)
    (hProb : ∀ i, p i ≤ 1)
    (hVZero : ∀ i, p i = 0 → V i = 0)
    (hVMean : ∀ i < n, V i ≤
      (n : ℝ) / ((n : ℝ) - (i : ℝ)))
    (hVTail : ∀ i < n, 0 < p i →
      V i ≤ 2 * p i * (1 + Real.log
        (2 * (n : ℝ) / (((n : ℝ) - (i : ℝ)) * p i)))) :
    t ≤ (Nat.log 2 m : ℝ) - 1 +
      (m : ℝ) / (2 : ℝ) ^ (Nat.log 2 m) +
      ∑ i ∈ Finset.range (Nat.log 2 m),
        weight (Nat.log 2 m) i * imbalanceBound n i := by
  obtain ⟨_, hle⟩ := nat_log_pos_and_le n m hm hsize
  apply theorem_4_4_main n m (Nat.log 2 m) t e p V
    hInit hRec hTail hProb
  intro i hi
  apply imbalance_of_lemma_4_3 n i (lt_of_lt_of_le hi hle)
    (p i) (V i) (hProbNonneg i) (hProb i) (hVZero i)
    (hVMean i (lt_of_lt_of_le hi hle))
    (hVTail i (lt_of_lt_of_le hi hle))

/-!
## A single entry point for Section 4

The next theorem packages the displayed inequality and (a)--(c).
Its proof assumptions correspond *only* to the probabilistic content of
Lemmas 4.1 and 4.3 and the elementary facts about probabilities.
No pre-combined imbalance inequality, floor-log fact or chord lemma is
assumed.
-/

/-- Theorem 4.4 and parts (a)--(c), assuming Lemmas 4.1 and 4.3.
The fourth conjunct states the conditional conclusion (c). -/
theorem theorem_4_4_all_from_probabilistic_lemmas (n m : ℕ)
    (t : ℝ) (e p V : ℕ → ℝ)
    (hm : 2 ≤ m) (hsize : m ≤ 2 ^ n)
    (hInit : e 0 = (m : ℝ) - 1)
    (hRec : ∀ i, e (i + 1) = (e i - p i + V i) / 2)
    (hTail : ∀ h, t ≤ (∑ i ∈ Finset.range h, p i) + e h)
    (hProbNonneg : ∀ i, 0 ≤ p i)
    (hProb : ∀ i, p i ≤ 1)
    (hVZero : ∀ i, p i = 0 → V i = 0)
    (hVMean : ∀ i < n, V i ≤
      (n : ℝ) / ((n : ℝ) - (i : ℝ)))
    (hVTail : ∀ i < n, 0 < p i →
      V i ≤ 2 * p i * (1 + Real.log
        (2 * (n : ℝ) / (((n : ℝ) - (i : ℝ)) * p i)))) :
    (t ≤ (Nat.log 2 m : ℝ) - 1 +
      (m : ℝ) / (2 : ℝ) ^ (Nat.log 2 m) +
      ∑ i ∈ Finset.range (Nat.log 2 m),
        weight (Nat.log 2 m) i * imbalanceBound n i) ∧
    (t < Real.logb 2 (m : ℝ) + 2 +
      2 * Real.log (2 * (Nat.log 2 m : ℝ))) ∧
    (t < Real.logb 2 (m : ℝ) + 1 +
      ((Nat.log 2 m : ℝ) - 1) /
      ((n : ℝ) - (Nat.log 2 m : ℝ) + 1)) ∧
    (2 * Nat.log 2 m - 2 ≤ n →
      t < Real.logb 2 (m : ℝ) + 2) := by
  obtain ⟨_, hle⟩ := nat_log_pos_and_le n m hm hsize
  have hV : ∀ i < Nat.log 2 m, V i ≤ imbalanceBound n i := by
    intro i hi
    have hin : i < n := lt_of_lt_of_le hi hle
    exact imbalance_of_lemma_4_3 n i hin (p i) (V i)
      (hProbNonneg i) (hProb i) (hVZero i)
      (hVMean i hin) (hVTail i hin)
  refine ⟨?_, ?_, ?_, ?_⟩
  · exact theorem_4_4_main n m (Nat.log 2 m) t e p V
      hInit hRec hTail hProb hV
  · exact theorem_4_4_a_nat n m t e p V hm hsize
      hInit hRec hTail hProb hV
  · exact theorem_4_4_b_nat n m t e p V hm hsize
      hInit hRec hTail hProb hV
  · intro hn
    exact theorem_4_4_c_nat n m t e p V hm hsize
      hInit hRec hTail hProb hV hn


end GradientKey

/-!
## Finite-uniform interface for the random path

A concrete `Ω` will eventually consist of pairs `(A,j)`, where `A` is an
injective binary table and `j` is a column.  This module deliberately does
not assume independence of rows, or any unproved inequality.  It uses only
finite sums and pointwise facts that any correctly constructed greedy path
must satisfy.

Compared with the earlier `theorem_4_4_all_from_probabilistic_lemmas`, this
interface proves `hInit`, `0 ≤ p_i ≤ 1`, `p_i=0 → V_i=0`, and the expected
tail inequality from a pointwise path-length bound.  It leaves the actual
conditional transition identity (Lemma 4.1) and the two hard imbalance
estimates (Lemma 4.3) as explicit obligations.
-/

namespace GradientKey

section FiniteUniform

variable {Ω : Type*} [Fintype Ω] [Nonempty Ω]

/-- Expectation under the uniform distribution on a nonempty finite type. -/
private noncomputable def finiteAverage (f : Ω → ℝ) : ℝ :=
  (∑ ω : Ω, f ω) / (Fintype.card Ω : ℝ)

private lemma finiteCard_pos : (0 : ℝ) < Fintype.card Ω := by
  exact_mod_cast (Fintype.card_pos : 0 < Fintype.card Ω)

private lemma finiteAverage_const (c : ℝ) :
    finiteAverage (Ω := Ω) (fun _ => c) = c := by
  have hcard : (Fintype.card Ω : ℝ) ≠ 0 :=
    ne_of_gt (finiteCard_pos (Ω := Ω))
  unfold finiteAverage
  simp only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
  exact mul_div_cancel_left₀ c hcard

private lemma finiteAverage_nonneg (f : Ω → ℝ)
    (hf : ∀ ω, 0 ≤ f ω) :
    0 ≤ finiteAverage f := by
  unfold finiteAverage
  exact div_nonneg
    (Finset.sum_nonneg (fun ω _ => hf ω))
    (le_of_lt (finiteCard_pos (Ω := Ω)))

private lemma finiteAverage_mono (f g : Ω → ℝ)
    (hfg : ∀ ω, f ω ≤ g ω) :
    finiteAverage f ≤ finiteAverage g := by
  unfold finiteAverage
  apply (div_le_div_iff₀ (finiteCard_pos (Ω := Ω))
    (finiteCard_pos (Ω := Ω))).2
  have hsum : (∑ ω : Ω, f ω) ≤ ∑ ω : Ω, g ω :=
    Finset.sum_le_sum (fun ω _ => hfg ω)
  exact mul_le_mul_of_nonneg_right hsum
    (le_of_lt (finiteCard_pos (Ω := Ω)))

private lemma finiteAverage_add (f g : Ω → ℝ) :
    finiteAverage (fun ω => f ω + g ω) =
      finiteAverage f + finiteAverage g := by
  unfold finiteAverage
  rw [Finset.sum_add_distrib, add_div]

private lemma finiteAverage_sum (h : ℕ) (f : ℕ → Ω → ℝ) :
    finiteAverage (fun ω => ∑ i ∈ Finset.range h, f i ω) =
      ∑ i ∈ Finset.range h, finiteAverage (f i) := by
  unfold finiteAverage
  rw [Finset.sum_comm, ← Finset.sum_div]

/-- Finite data required from a path through a decision tree.  The
separate `pathTail` property is pointwise, not probabilistic. -/
structure FinitePathData (Ω : Type*) (m : ℕ) where
  size : Ω → ℕ → ℕ
  imbalance : Ω → ℕ → ℝ
  depth : Ω → ℝ
  size_zero : ∀ ω, size ω 0 = m
  imbalance_zero_leaf : ∀ ω i, size ω i < 2 → imbalance ω i = 0
  pathTail : ∀ ω h, depth ω ≤
    (∑ i ∈ Finset.range h, (if 2 ≤ size ω i then (1 : ℝ) else 0)) +
      ((size ω h : ℝ) - 1)

namespace FinitePathData

variable {m : ℕ} (P : FinitePathData Ω m)

/-- Expected size minus one. -/
noncomputable def expectedExcess (i : ℕ) : ℝ :=
  finiteAverage (fun ω => (P.size ω i : ℝ) - 1)

/-- Probability that the sampled path contains a fork at depth `i`. -/
noncomputable def forkProb (i : ℕ) : ℝ :=
  finiteAverage (fun ω => if 2 ≤ P.size ω i then (1 : ℝ) else 0)

/-- Expected split imbalance, extended by zero at leaves. -/
noncomputable def expectedImbalance (i : ℕ) : ℝ :=
  finiteAverage (fun ω => P.imbalance ω i)

/-- Expected path length. -/
noncomputable def expectedDepth : ℝ :=
  finiteAverage P.depth

theorem expectedExcess_zero : P.expectedExcess 0 = (m : ℝ) - 1 := by
  have hfun : (fun ω : Ω => (P.size ω 0 : ℝ) - 1) =
      (fun _ : Ω => (m : ℝ) - 1) := by
    funext ω
    rw [P.size_zero ω]
  change finiteAverage (fun ω : Ω => (P.size ω 0 : ℝ) - 1) = (m : ℝ) - 1
  rw [hfun]
  exact finiteAverage_const ((m : ℝ) - 1)

theorem forkProb_nonneg (i : ℕ) : 0 ≤ P.forkProb i := by
  unfold forkProb
  apply finiteAverage_nonneg
  intro ω
  split_ifs <;> norm_num

theorem forkProb_le_one (i : ℕ) : P.forkProb i ≤ 1 := by
  have h : P.forkProb i ≤ finiteAverage (fun _ : Ω => (1 : ℝ)) := by
    unfold forkProb
    apply finiteAverage_mono
    intro ω
    split_ifs <;> norm_num
  simpa only [finiteAverage_const] using h

/-- This is a consequence of the definition of fork probability and
pointwise vanishing of imbalance at a leaf; no estimate is assumed. -/
theorem expectedImbalance_zero (i : ℕ) (hp : P.forkProb i = 0) :
    P.expectedImbalance i = 0 := by
  have hn : ∀ ω : Ω, P.size ω i < 2 := by
    intro ω
    by_contra hnot
    have hfork : 2 ≤ P.size ω i := Nat.le_of_not_gt hnot
    have hsum : (1 : ℝ) ≤
        ∑ ω' : Ω, (if 2 ≤ P.size ω' i then (1 : ℝ) else 0) := by
      have hsingle := Finset.single_le_sum
        (s := (Finset.univ : Finset Ω))
        (f := fun ω' => if 2 ≤ P.size ω' i then (1 : ℝ) else 0)
        (fun ω' _ => by split_ifs <;> norm_num)
        (Finset.mem_univ ω)
      simpa [hfork] using hsingle
    have hpositive : 0 < P.forkProb i := by
      unfold forkProb finiteAverage
      exact div_pos (by linarith only [hsum])
        (finiteCard_pos (Ω := Ω))
    linarith only [hp, hpositive]
  have hz : (fun ω : Ω => P.imbalance ω i) = (fun _ => (0 : ℝ)) := by
    funext ω
    exact P.imbalance_zero_leaf ω i (hn ω)
  unfold expectedImbalance
  rw [hz]
  exact finiteAverage_const 0

/-- The expected tail inequality of Lemma 4.1 follows by averaging the
pointwise path-length bound and interchanging two *finite* sums. -/
theorem expectedTail (h : ℕ) :
    P.expectedDepth ≤
      (∑ i ∈ Finset.range h, P.forkProb i) + P.expectedExcess h := by
  have havg := finiteAverage_mono
    (f := P.depth)
    (g := fun ω : Ω =>
      (∑ i ∈ Finset.range h,
        (if 2 ≤ P.size ω i then (1 : ℝ) else 0)) +
        ((P.size ω h : ℝ) - 1))
    (fun ω => P.pathTail ω h)
  rw [finiteAverage_add, finiteAverage_sum] at havg
  exact havg

end FinitePathData

/-- The full statement of Theorem 4.4 for a finite uniform path model.
The initial expectation, probability bounds, zero-if-no-fork property,
and expected tail bound are all proved above.  Only the transition
identity and the two nontrivial estimates of Lemma 4.3 remain hypotheses. -/
theorem theorem_4_4_from_finite_paths
    (n m : ℕ) (hm : 2 ≤ m) (hsize : m ≤ 2 ^ n)
    (P : FinitePathData Ω m)
    (hTransition : ∀ i,
      P.expectedExcess (i + 1) =
        (P.expectedExcess i - P.forkProb i + P.expectedImbalance i) / 2)
    (hVMean : ∀ i < n,
      P.expectedImbalance i ≤ (n : ℝ) / ((n : ℝ) - (i : ℝ)))
    (hVTail : ∀ i < n, 0 < P.forkProb i →
      P.expectedImbalance i ≤
        2 * P.forkProb i * (1 + Real.log
          (2 * (n : ℝ) /
            (((n : ℝ) - (i : ℝ)) * P.forkProb i)))) :
    (P.expectedDepth ≤ (Nat.log 2 m : ℝ) - 1 +
      (m : ℝ) / (2 : ℝ) ^ (Nat.log 2 m) +
      ∑ i ∈ Finset.range (Nat.log 2 m),
        weight (Nat.log 2 m) i * imbalanceBound n i) ∧
    (P.expectedDepth < Real.logb 2 (m : ℝ) + 2 +
      2 * Real.log (2 * (Nat.log 2 m : ℝ))) ∧
    (P.expectedDepth < Real.logb 2 (m : ℝ) + 1 +
      ((Nat.log 2 m : ℝ) - 1) /
      ((n : ℝ) - (Nat.log 2 m : ℝ) + 1)) ∧
    (2 * Nat.log 2 m - 2 ≤ n →
      P.expectedDepth < Real.logb 2 (m : ℝ) + 2) := by
  exact theorem_4_4_all_from_probabilistic_lemmas n m
    P.expectedDepth P.expectedExcess P.forkProb P.expectedImbalance
    hm hsize P.expectedExcess_zero hTransition P.expectedTail
    P.forkProb_nonneg P.forkProb_le_one P.expectedImbalance_zero
    hVMean hVTail

end FiniteUniform

end GradientKey

/-!
## First structural fact behind Lemma 4.2

Fix the table `B` obtained by deleting a row, and write `x` for the
missing row.  Distinctness of the original columns is equivalent to
requiring `x a ≠ x b` whenever `a ≠ b` and `B` has equal columns `a,b`.
As `x` has only two possible values, any equality class of `B` has size
at most two.  Both facts are formalized here independently of probability.
-/

namespace GradientKey.RowDeletion

variable {n m : ℕ}

/-- Binary table after removing one row. -/
abbrev RemainingTable (n m : ℕ) := Fin n → Fin m → Bool

/-- `B` agrees in every remaining row on columns `a,b`. -/
def SameColumn (B : RemainingTable n m) (a b : Fin m) : Prop :=
  ∀ r, B r a = B r b

/-- Valid choices of the deleted row, preserving column distinctness. -/
def ValidExtension (B : RemainingTable n m) (x : Fin m → Bool) : Prop :=
  ∀ a b, a ≠ b → SameColumn B a b → x a ≠ x b

/-- A deleted row makes the full columns distinct precisely when it
separates all distinct pairs of columns that became equal in `B`. -/
theorem validExtension_iff (B : RemainingTable n m) (x : Fin m → Bool) :
    ValidExtension B x ↔
      ∀ a b, SameColumn B a b → x a = x b → a = b := by
  constructor
  · intro h a b hB hx
    by_contra hne
    exact h a b hne hB hx
  · intro h a b hne hB hx
    exact hne (h a b hB hx)

/-- If an admissible deleted row exists, no three *distinct* columns
can be equal in the remaining table. This is the first claim of Lemma 4.2. -/
theorem no_three_equal_columns
    (B : RemainingTable n m) (x : Fin m → Bool)
    (hx : ValidExtension B x) (a b c : Fin m)
    (hab : SameColumn B a b) (hac : SameColumn B a c) :
    a = b ∨ a = c ∨ b = c := by
  by_contra h
  push_neg at h
  obtain ⟨hneab, hneac, hnebc⟩ := h
  have hbc : SameColumn B b c := by
    intro r
    exact (hab r).symm.trans (hac r)
  have hxab : x a ≠ x b := hx a b hneab hab
  have hxac : x a ≠ x c := hx a c hneac hac
  have hxbc : x b ≠ x c := hx b c hnebc hbc
  cases ha : x a <;> cases hb : x b <;> cases hc : x c <;>
    simp_all

/-- The formulation used by the paper: a positive-probability row
extension must exist, and existence alone rules out equality classes
with three members. -/
theorem admissible_exists_implies_no_three
    (B : RemainingTable n m)
    (hex : ∃ x : Fin m → Bool, ValidExtension B x)
    (a b c : Fin m)
    (hab : SameColumn B a b) (hac : SameColumn B a c) :
    a = b ∨ a = c ∨ b = c := by
  obtain ⟨x, hx⟩ := hex
  exact no_three_equal_columns B x hx a b c hab hac

end GradientKey.RowDeletion

/-!
## Concrete binary tables and the greedy path

The next definitions make the intended finite sample space explicit.
`greedyRow` uses Mathlib's `List.argmax`, which retains the first entry
when scores tie, applied to the rows in increasing order.  The recursive
`candidateAt` function is therefore the path followed by column `j`,
provided the table has distinct columns.

These definitions do *not* by themselves prove the three deep assumptions
of Theorem 4.4.  In particular, a formal proof that every non-singleton
candidate set is split, that the path ends within `n` rows, and that
row-deletion yields the Lemma 4.3 bounds is still required.
-/

namespace GradientKey.Concrete

variable {n m : ℕ}

/-- An `n × m` binary matrix. -/
abbrev Table (n m : ℕ) := Fin n → Fin m → Bool

/-- The `m` column-vectors are pairwise distinct. -/
def DistinctColumns (A : Table n m) : Prop :=
  Function.Injective (fun j : Fin m => fun r : Fin n => A r j)

/-- The finite set of valid tables, encoded as a subtype. -/
abbrev ValidTable (n m : ℕ) := { A : Table n m // DistinctColumns A }

/-- Uniform samples consist of a valid table and a column index. -/
abbrev Sample (n m : ℕ) := ValidTable n m × Fin m

noncomputable instance sampleFintype (n m : ℕ) : Fintype (Sample n m) := by
  classical
  infer_instance

/-- Number of ones on a given candidate set. -/
def ones (A : Table n m) (S : Finset (Fin m)) (r : Fin n) : ℕ :=
  (S.filter (fun j => A r j = true)).card

/-- Number of zeros on a given candidate set. -/
def zeros (A : Table n m) (S : Finset (Fin m)) (r : Fin n) : ℕ :=
  (S.filter (fun j => A r j = false)).card

/-- The row quality used in the article. -/
def quality (A : Table n m) (S : Finset (Fin m)) (r : Fin n) : ℕ :=
  min (ones A S r) (zeros A S r)

/-- Select the first row of maximal quality. `hn` supplies a fallback
only to make the empty-list case of `List.argmax` well-typed. -/
noncomputable def greedyRow (A : Table n m) (S : Finset (Fin m))
    (hn : 0 < n) : Fin n :=
  (List.argmax (quality A S) (List.finRange n)).getD ⟨0, hn⟩

/-- Advance one step along the path of the chosen column. -/
noncomputable def candidateStep (A : Table n m) (S : Finset (Fin m))
    (j : Fin m) (hn : 0 < n) : Finset (Fin m) := by
  classical
  exact if S.card ≤ 1 then S
    else S.filter (fun k => A (greedyRow A S hn) k = A (greedyRow A S hn) j)

/-- Candidate set at a depth, continued constantly after a singleton. -/
noncomputable def candidateAt (A : Table n m) (j : Fin m)
    (hn : 0 < n) : ℕ → Finset (Fin m)
  | 0 => Finset.univ
  | i + 1 => candidateStep A (candidateAt A j hn i) j hn

/-- The split imbalance, defined to be zero at leaves. -/
noncomputable def localImbalance (A : Table n m) (S : Finset (Fin m))
    (hn : 0 < n) : ℝ :=
  if S.card < 2 then 0
  else (((S.card : ℝ) - 2 * (ones A S (greedyRow A S hn) : ℝ)) ^ 2) /
    (S.card : ℝ)

/-- Number of actual forks in the first `n` steps of the path. -/
noncomputable def pathDepth (A : Table n m) (j : Fin m)
    (hn : 0 < n) : ℝ :=
  (((Finset.range n).filter
    (fun i => 2 ≤ (candidateAt A j hn i).card)).card : ℝ)

/-- Candidate size of a uniformly sampled table-column pair. -/
noncomputable def sampleSize (hn : 0 < n) (ω : Sample n m) (i : ℕ) : ℕ :=
  (candidateAt ω.1.1 ω.2 hn i).card

/-- Split imbalance along a sampled path. -/
noncomputable def sampleImbalance (hn : 0 < n)
    (ω : Sample n m) (i : ℕ) : ℝ :=
  localImbalance ω.1.1 (candidateAt ω.1.1 ω.2 hn i) hn

/-- Path length of a sampled table-column pair. -/
noncomputable def sampleDepth (hn : 0 < n) (ω : Sample n m) : ℝ :=
  pathDepth ω.1.1 ω.2 hn

/-- The initial candidate set contains all `m` columns. -/
theorem sampleSize_zero (hn : 0 < n) (ω : Sample n m) :
    sampleSize hn ω 0 = m := by
  simp [sampleSize, candidateAt]

/-- At a leaf the imbalance is identically zero. -/
theorem sampleImbalance_zero_leaf (hn : 0 < n)
    (ω : Sample n m) (i : ℕ)
    (h : sampleSize hn ω i < 2) :
    sampleImbalance hn ω i = 0 := by
  simpa [sampleImbalance, localImbalance, sampleSize, h]

/-- Bridge the concrete greedy path to the finite-uniform theorem.
`hTail` is the remaining *pointwise* tree argument from Lemma 4.1. -/
noncomputable def finitePathData (hn : 0 < n)
    (hTail : ∀ ω : Sample n m, ∀ h,
      sampleDepth hn ω ≤
        (∑ i ∈ Finset.range h,
          (if 2 ≤ sampleSize hn ω i then (1 : ℝ) else 0)) +
        ((sampleSize hn ω h : ℝ) - 1)) :
    FinitePathData (Sample n m) m :=
  { size := sampleSize hn
    imbalance := sampleImbalance hn
    depth := sampleDepth hn
    size_zero := sampleSize_zero hn
    imbalance_zero_leaf := sampleImbalance_zero_leaf hn
    pathTail := hTail }

end GradientKey.Concrete

/-!
## Second-moment algebra for Lemma 4.2

Once one identifies the singleton columns in a row-deleted table,
the quantity `s - 2k` is the sum of independent fair signs on these
singleton columns.  The independence is still to be established from
the row-extension bijection. The following *finite algebra* needs only
pairwise orthogonality of the signs, and yields the exact value of the
conditional mean squared imbalance, `f/s ≤ 1`.
-/

namespace GradientKey

section SecondMoment

variable {Ω : Type*} [Fintype Ω] [Nonempty Ω]

private lemma finiteAverage_finset_sum {ι : Type*}
    (s : Finset ι) (f : ι → Ω → ℝ) :
    finiteAverage (fun ω => ∑ a ∈ s, f a ω) =
      ∑ a ∈ s, finiteAverage (f a) := by
  unfold finiteAverage
  rw [Finset.sum_comm, ← Finset.sum_div]

private lemma finiteAverage_div (f : Ω → ℝ) (c : ℝ) :
    finiteAverage (fun ω => f ω / c) = finiteAverage f / c := by
  unfold finiteAverage
  rw [Finset.sum_div]
  ring

/-- Exact second moment of a finite family of pairwise orthogonal
unit signs under a finite uniform distribution. -/
theorem pairwise_orthogonal_signs_second_moment
    {ι : Type*} [DecidableEq ι] (s : Finset ι)
    (X : ι → Ω → ℝ)
    (hSquare : ∀ a ∈ s, ∀ ω, (X a ω) ^ 2 = 1)
    (hCross : ∀ a ∈ s, ∀ b ∈ s, a ≠ b →
      finiteAverage (fun ω => X a ω * X b ω) = 0) :
    finiteAverage (fun ω => (∑ a ∈ s, X a ω) ^ 2) = (s.card : ℝ) := by
  classical
  have hDiag : ∀ a ∈ s,
      finiteAverage (fun ω => X a ω * X a ω) = 1 := by
    intro a ha
    have hfun : (fun ω : Ω => X a ω * X a ω) = (fun _ => (1 : ℝ)) := by
      funext ω
      simpa only [pow_two] using hSquare a ha ω
    rw [hfun]
    exact finiteAverage_const (Ω := Ω) 1
  have hInner : ∀ a ∈ s,
      (∑ b ∈ s, finiteAverage (fun ω => X a ω * X b ω)) = 1 := by
    intro a ha
    calc
      (∑ b ∈ s, finiteAverage (fun ω => X a ω * X b ω)) =
          ∑ b ∈ s, (if a = b then (1 : ℝ) else 0) := by
            apply Finset.sum_congr rfl
            intro b hb
            by_cases hab : a = b
            · subst b
              simpa using hDiag a ha
            · simpa [hab] using hCross a ha b hb hab
      _ = 1 := by simp [ha]
  calc
    finiteAverage (fun ω => (∑ a ∈ s, X a ω) ^ 2) =
        finiteAverage (fun ω =>
          ∑ a ∈ s, ∑ b ∈ s, X a ω * X b ω) := by
            congr 1
            funext ω
            simp only [pow_two, Finset.sum_mul_sum]
    _ = ∑ a ∈ s, ∑ b ∈ s,
        finiteAverage (fun ω => X a ω * X b ω) := by
          rw [finiteAverage_finset_sum]
          apply Finset.sum_congr rfl
          intro a ha
          rw [finiteAverage_finset_sum]
    _ = ∑ a ∈ s, (1 : ℝ) := by
          apply Finset.sum_congr rfl
          intro a ha
          exact hInner a ha
    _ = (s.card : ℝ) := by simp

/-- The bound `E[v_r(S)] ≤ 1` from Lemma 4.2, expressed using the
pairwise-orthogonal fair signs on the `f` singleton columns. The actual
row-deletion probability law must still supply `hSquare` and `hCross`. -/
theorem fixed_row_mean_imbalance_le_one
    {ι : Type*} [DecidableEq ι]
    (free : Finset ι) (X : ι → Ω → ℝ) (s : ℕ)
    (hs : 0 < s) (hfs : free.card ≤ s)
    (hSquare : ∀ a ∈ free, ∀ ω, (X a ω) ^ 2 = 1)
    (hCross : ∀ a ∈ free, ∀ b ∈ free, a ≠ b →
      finiteAverage (fun ω => X a ω * X b ω) = 0) :
    finiteAverage (fun ω =>
      (∑ a ∈ free, X a ω) ^ 2 / (s : ℝ)) ≤ 1 := by
  have hMoment := pairwise_orthogonal_signs_second_moment
    (Ω := Ω) free X hSquare hCross
  have hsR : (0 : ℝ) < s := by exact_mod_cast hs
  have hfsR : (free.card : ℝ) ≤ (s : ℝ) := by exact_mod_cast hfs
  calc
    finiteAverage (fun ω =>
      (∑ a ∈ free, X a ω) ^ 2 / (s : ℝ)) =
        finiteAverage (fun ω => (∑ a ∈ free, X a ω) ^ 2) / (s : ℝ) :=
          finiteAverage_div _ _
    _ = (free.card : ℝ) / (s : ℝ) := by rw [hMoment]
    _ ≤ 1 := (div_le_one hsR).2 hfsR

end SecondMoment

end GradientKey
/-!
## Row-deletion symmetry: the missing second-moment hypotheses

Fix a table `B` obtained by deleting a row, and consider the finite type of
rows that restore pairwise distinctness.  If column `a` of `B` is unique, then
flipping bit `a` of an admissible row preserves admissibility.  Reindexing the
finite sum with this involution proves that the sign at `a` is unbiased and
uncorrelated with the sign at every other column.  Consequently the previously
formalized second-moment lemma applies *without* orthogonality assumptions.

The remaining step for the exact formulation of Lemma 4.2 is a cancellation
identity for duplicated pairs inside a candidate set, as well as the
Hoeffding tail estimate.  Those are not claimed below.
-/

namespace GradientKey

/-- A sign-reversing equivalence pairs the terms of a finite sum. -/
private theorem sum_eq_zero_of_neg_equiv
    {Ω : Type*} [Fintype Ω] (e : Ω ≃ Ω) (f : Ω → ℝ)
    (hf : ∀ ω, f (e ω) = -f ω) :
    (∑ ω : Ω, f ω) = 0 := by
  have hReindex : (∑ ω : Ω, f (e ω)) = ∑ ω : Ω, f ω :=
    Equiv.sum_comp e f
  have hNeg : (∑ ω : Ω, f (e ω)) = -(∑ ω : Ω, f ω) := by
    calc
      (∑ ω : Ω, f (e ω)) = ∑ ω : Ω, -f ω := by
        apply Finset.sum_congr rfl
        intro ω _
        exact hf ω
      _ = -(∑ ω : Ω, f ω) := by rw [Finset.sum_neg_distrib]
  linarith

namespace RowDeletion

variable {n m : ℕ}

/-- A column which occurs only once among the columns of the deleted-row table. -/
def UniqueColumn (B : RemainingTable n m) (a : Fin m) : Prop :=
  ∀ b, SameColumn B a b → b = a

/-- Toggle one coordinate of the missing row. -/
def flipBit (a : Fin m) (x : Fin m → Bool) : Fin m → Bool :=
  fun b => if b = a then !x b else x b

theorem flipBit_twice (a : Fin m) (x : Fin m → Bool) :
    flipBit a (flipBit a x) = x := by
  funext b
  by_cases hb : b = a
  · subst b
    simp [flipBit]
  · simp [flipBit, hb]

/-- A unique column cannot participate in any pair that the deleted
row must separate. Hence its bit can be flipped freely. -/
theorem flipBit_preserves_extension
    (B : RemainingTable n m) (a : Fin m)
    (ha : UniqueColumn B a) (x : Fin m → Bool)
    (hx : ValidExtension B x) :
    ValidExtension B (flipBit a x) := by
  intro u v huv hB
  have hua : u ≠ a := by
    intro h
    subst u
    exact huv (ha v hB).symm
  have hva : v ≠ a := by
    intro h
    subst v
    exact huv (ha u (fun r => (hB r).symm))
  simpa [flipBit, hua, hva] using hx u v huv hB

/-- The finite collection of possible inserted rows, conditioned on the
remaining table. If nonempty, the original uniform table model makes
this type uniform. -/
abbrev Extension (B : RemainingTable n m) :=
  { x : Fin m → Bool // ValidExtension B x }

noncomputable instance extensionFintype (B : RemainingTable n m) :
    Fintype (Extension B) := by
  classical
  infer_instance

/-- Flip of a unique bit, now as a permutation of valid extensions. -/
def flipExtension (B : RemainingTable n m) (a : Fin m)
    (ha : UniqueColumn B a) : Extension B ≃ Extension B where
  toFun := fun x => ⟨flipBit a x.1,
    flipBit_preserves_extension B a ha x.1 x.2⟩
  invFun := fun x => ⟨flipBit a x.1,
    flipBit_preserves_extension B a ha x.1 x.2⟩
  left_inv := by
    intro x
    apply Subtype.ext
    exact flipBit_twice a x.1
  right_inv := by
    intro x
    apply Subtype.ext
    exact flipBit_twice a x.1

/-- Encode an inserted-row bit as a real Rademacher sign. -/
def signedBit (x : Fin m → Bool) (a : Fin m) : ℝ :=
  if x a then 1 else -1

theorem signedBit_square (x : Fin m → Bool) (a : Fin m) :
    (signedBit x a) ^ 2 = 1 := by
  cases h : x a <;> simp [signedBit, h]

theorem signedBit_flip_same (x : Fin m → Bool) (a : Fin m) :
    signedBit (flipBit a x) a = -(signedBit x a) := by
  cases h : x a <;> simp [signedBit, flipBit, h]

theorem signedBit_flip_other (x : Fin m → Bool)
    (a b : Fin m) (hba : b ≠ a) :
    signedBit (flipBit a x) b = signedBit x b := by
  simp [signedBit, flipBit, hba]

/-- Conditioning on a fixed deleted-row table makes every unique-column
bit unbiased.  This is a finite-sum statement, not an independence axiom. -/
theorem conditional_unique_sign_mean_zero
    (B : RemainingTable n m) [Nonempty (Extension B)]
    (a : Fin m) (ha : UniqueColumn B a) :
    finiteAverage (Ω := Extension B)
      (fun x => signedBit x.1 a) = 0 := by
  have hZero : (∑ x : Extension B, signedBit x.1 a) = 0 := by
    apply sum_eq_zero_of_neg_equiv (flipExtension B a ha)
    intro x
    change signedBit (flipBit a x.1) a = -signedBit x.1 a
    exact signedBit_flip_same x.1 a
  unfold finiteAverage
  rw [hZero]
  simp

/-- Two distinct columns have zero signed cross-moment whenever the first
is unique in `B`. In particular, different unique columns are orthogonal. -/
theorem conditional_unique_sign_cross_zero
    (B : RemainingTable n m) [Nonempty (Extension B)]
    (a b : Fin m) (ha : UniqueColumn B a) (hab : a ≠ b) :
    finiteAverage (Ω := Extension B)
      (fun x => signedBit x.1 a * signedBit x.1 b) = 0 := by
  have hZero :
      (∑ x : Extension B, signedBit x.1 a * signedBit x.1 b) = 0 := by
    apply sum_eq_zero_of_neg_equiv (flipExtension B a ha)
    intro x
    change signedBit (flipBit a x.1) a *
      signedBit (flipBit a x.1) b =
      -(signedBit x.1 a * signedBit x.1 b)
    rw [signedBit_flip_same, signedBit_flip_other x.1 a b hab.symm]
    ring
  unfold finiteAverage
  rw [hZero]
  simp

/-- The unique columns inside a candidate set. -/
noncomputable def uniqueIn (B : RemainingTable n m)
    (S : Finset (Fin m)) : Finset (Fin m) := by
  classical
  exact S.filter (UniqueColumn B)

/-- The squared sum of all unique-column signs has *exact* conditional
expectation equal to the number of unique columns. -/
theorem conditional_unique_signs_second_moment
    (B : RemainingTable n m) [Nonempty (Extension B)]
    (S : Finset (Fin m)) :
    finiteAverage (Ω := Extension B)
      (fun x => (∑ a ∈ uniqueIn B S, signedBit x.1 a) ^ 2) =
      ((uniqueIn B S).card : ℝ) := by
  classical
  apply pairwise_orthogonal_signs_second_moment
    (Ω := Extension B) (uniqueIn B S)
    (fun a x => signedBit x.1 a)
  · intro a ha x
    exact signedBit_square x.1 a
  · intro a ha b hb hab
    apply conditional_unique_sign_cross_zero B a b
    · exact (Finset.mem_filter.mp ha).2
    · exact hab

/-- Lemma 4.2's *mean* bound for the free-sign contribution, with
no orthogonality hypotheses: these are supplied by the flip symmetry. -/
theorem conditional_free_sign_imbalance_le_one
    (B : RemainingTable n m) [Nonempty (Extension B)]
    (S : Finset (Fin m)) (hS : 0 < S.card) :
    finiteAverage (Ω := Extension B)
      (fun x =>
        (∑ a ∈ uniqueIn B S, signedBit x.1 a) ^ 2 /
          (S.card : ℝ)) ≤ 1 := by
  classical
  have hsub : uniqueIn B S ⊆ S := by
    intro a ha
    exact (Finset.mem_filter.mp ha).1
  have hcard : (uniqueIn B S).card ≤ S.card :=
    Finset.card_le_card hsub
  apply fixed_row_mean_imbalance_le_one
    (Ω := Extension B) (uniqueIn B S)
    (fun a x => signedBit x.1 a) S.card hS hcard
  · intro a ha x
    exact signedBit_square x.1 a
  · intro a ha b hb hab
    exact conditional_unique_sign_cross_zero B a b
      ((Finset.mem_filter.mp ha).2) hab

end RowDeletion
end GradientKey
/-!
## Cancellation of duplicate pairs in a candidate set

If the deleted-row table has an admissible extension, every nonunique
column has exactly one distinct twin. On a candidate set closed under
column equality, the two opposite signs of each pair cancel. Therefore
the signed sum over *all* candidate columns equals the signed sum over
unique columns. Together with the preceding symmetry lemmas this proves
the fixed-row **mean** estimate of Lemma 4.2 for the signed-sum version of
split imbalance (the paper's `(s-2k)^2/s` is the same expression).
-/

namespace GradientKey.RowDeletion

variable {n m : ℕ}

/-- Failure of uniqueness supplies another column with the same remaining
bits. -/
theorem nonunique_has_partner (B : RemainingTable n m) (a : Fin m)
    (ha : ¬ UniqueColumn B a) :
    ∃ b : Fin m, b ≠ a ∧ SameColumn B a b := by
  classical
  by_contra h
  apply ha
  intro b hb
  by_contra hne
  exact h ⟨b, hne, hb⟩

/-- Choose the (necessarily unique, for an admissible deleted-row table)
twin of a nonunique column; fix the unique columns. -/
noncomputable def partner (B : RemainingTable n m) (a : Fin m) : Fin m :=
  if h : UniqueColumn B a then a
  else Classical.choose (nonunique_has_partner B a h)

theorem partner_of_nonunique (B : RemainingTable n m) (a : Fin m)
    (ha : ¬ UniqueColumn B a) :
    partner B a ≠ a ∧ SameColumn B a (partner B a) := by
  have hspec := Classical.choose_spec (nonunique_has_partner B a ha)
  simpa only [partner, dif_neg ha] using hspec

theorem partner_nonunique (B : RemainingTable n m) (a : Fin m)
    (ha : ¬ UniqueColumn B a) :
    ¬ UniqueColumn B (partner B a) := by
  obtain ⟨hne, hsame⟩ := partner_of_nonunique B a ha
  intro hunique
  have hback : SameColumn B (partner B a) a := by
    intro r
    exact (hsame r).symm
  exact hne (hunique a hback).symm

/-- The same-column classes are either singletons or pairs, so the
chosen partner is an involution when a valid extension exists. -/
theorem partner_twice (B : RemainingTable n m)
    (x : Fin m → Bool) (hx : ValidExtension B x) (a : Fin m) :
    partner B (partner B a) = a := by
  classical
  by_cases ha : UniqueColumn B a
  · simp [partner, ha]
  · obtain ⟨hneq, hsame⟩ := partner_of_nonunique B a ha
    have hb := partner_nonunique B a ha
    obtain ⟨hneq2, hsame2⟩ := partner_of_nonunique B (partner B a) hb
    have hback : SameColumn B (partner B a) a := by
      intro r
      exact (hsame r).symm
    have hthree := no_three_equal_columns B x hx
      (partner B a) a (partner B (partner B a)) hback hsame2
    rcases hthree with hba | hbc | hac
    · exact False.elim (hneq hba.symm)
    · exact False.elim (hneq2 hbc.symm)
    · exact hac.symm

/-- Candidate sets of the row-deleted greedy tree have this property:
they contain either both or neither columns of each remaining equal pair. -/
def PairClosed (B : RemainingTable n m) (S : Finset (Fin m)) : Prop :=
  ∀ a b, a ∈ S → SameColumn B a b → b ∈ S

noncomputable def repeatedIn (B : RemainingTable n m)
    (S : Finset (Fin m)) : Finset (Fin m) := by
  classical
  exact S.filter (fun a => ¬ UniqueColumn B a)

private theorem signedBit_opposite
    (x : Fin m → Bool) (a b : Fin m) (h : x a ≠ x b) :
    signedBit x a + signedBit x b = 0 := by
  cases ha : x a <;> cases hb : x b <;>
    simp_all [signedBit]

/-- The total contribution of repeated columns cancels identically
for each admissible extension, not merely on average. -/
theorem duplicate_sign_sum_zero
    (B : RemainingTable n m) (x : Fin m → Bool)
    (hx : ValidExtension B x) (S : Finset (Fin m))
    (hclosed : PairClosed B S) :
    (∑ a ∈ repeatedIn B S, signedBit x a) = 0 := by
  classical
  apply Finset.sum_involution
    (s := repeatedIn B S) (f := fun a => signedBit x a)
    (g := fun a _ => partner B a)
  · intro a ha
    have hna : ¬ UniqueColumn B a := (Finset.mem_filter.mp ha).2
    obtain ⟨hneq, hsame⟩ := partner_of_nonunique B a hna
    exact signedBit_opposite x a (partner B a)
      (hx a (partner B a) hneq hsame)
  · intro a ha _
    exact (partner_of_nonunique B a (Finset.mem_filter.mp ha).2).1
  · intro a ha
    have hna : ¬ UniqueColumn B a := (Finset.mem_filter.mp ha).2
    have hSa : a ∈ S := (Finset.mem_filter.mp ha).1
    have hpair : SameColumn B a (partner B a) :=
      (partner_of_nonunique B a hna).2
    change partner B a ∈ repeatedIn B S
    exact Finset.mem_filter.mpr
      ⟨hclosed a (partner B a) hSa hpair, partner_nonunique B a hna⟩
  · intro a ha
    exact partner_twice B x hx a

/-- The full signed row imbalance depends only on the unique columns
when the candidate set is closed under remaining equal-column classes. -/
theorem all_signs_eq_unique_signs
    (B : RemainingTable n m) (x : Fin m → Bool)
    (hx : ValidExtension B x) (S : Finset (Fin m))
    (hclosed : PairClosed B S) :
    (∑ a ∈ S, signedBit x a) =
      ∑ a ∈ uniqueIn B S, signedBit x a := by
  classical
  have hPartition := Finset.sum_filter_add_sum_filter_not S
    (UniqueColumn B) (fun a => signedBit x a)
  have hRepeat : (∑ a ∈ repeatedIn B S, signedBit x a) = 0 :=
    duplicate_sign_sum_zero B x hx S hclosed
  change (∑ a ∈ uniqueIn B S, signedBit x a) +
    (∑ a ∈ repeatedIn B S, signedBit x a) =
      (∑ a ∈ S, signedBit x a) at hPartition
  rw [hRepeat, add_zero] at hPartition
  exact hPartition.symm

/-- Full fixed-row mean estimate in Lemma 4.2, as an exact expression
in Rademacher signs. No independence or moment hypothesis is assumed. -/
theorem conditional_signed_imbalance_le_one
    (B : RemainingTable n m) [Nonempty (Extension B)]
    (S : Finset (Fin m)) (hS : 0 < S.card)
    (hclosed : PairClosed B S) :
    finiteAverage (Ω := Extension B)
      (fun x => (∑ a ∈ S, signedBit x.1 a) ^ 2 / (S.card : ℝ)) ≤ 1 := by
  have hfn :
      (fun x : Extension B =>
        (∑ a ∈ S, signedBit x.1 a) ^ 2 / (S.card : ℝ)) =
      (fun x : Extension B =>
        (∑ a ∈ uniqueIn B S, signedBit x.1 a) ^ 2 /
          (S.card : ℝ)) := by
    funext x
    rw [all_signs_eq_unique_signs B x.1 x.2 S hclosed]
  rw [hfn]
  exact conditional_free_sign_imbalance_le_one B S hS

end GradientKey.RowDeletion
/-!
## Convert signs back to the paper's `(s - 2k)^2 / s`

The sign sum counts each one as +1 and each zero as -1, hence equals
`2k - s`.  Its square is therefore exactly the article's split imbalance.
This makes the preceding conditional mean bound a theorem in the exact
notation of Lemma 4.2 rather than only in sign notation.
-/

namespace GradientKey.RowDeletion

variable {n m : ℕ}

/-- Number of ones of the inserted row in a set of candidate columns. -/
def insertedOnes (x : Fin m → Bool) (S : Finset (Fin m)) : ℕ :=
  (S.filter (fun a => x a = true)).card

/-- The imbalance of the inserted row, as defined in Section 4. -/
noncomputable def insertedImbalance (x : Fin m → Bool)
    (S : Finset (Fin m)) : ℝ :=
  (((S.card : ℝ) - 2 * (insertedOnes x S : ℝ)) ^ 2) /
    (S.card : ℝ)

private theorem signed_sum_eq_counts (x : Fin m → Bool)
    (S : Finset (Fin m)) :
    (∑ a ∈ S, signedBit x a) =
      2 * (insertedOnes x S : ℝ) - (S.card : ℝ) := by
  classical
  induction S using Finset.induction_on with
  | empty => simp [insertedOnes]
  | @insert a S ha ih =>
      cases h : x a <;>
        simp [insertedOnes, Finset.filter_insert, signedBit,
          h, ha, ih] <;> push_cast <;> ring

theorem insertedImbalance_eq_signed (x : Fin m → Bool)
    (S : Finset (Fin m)) :
    insertedImbalance x S =
      (∑ a ∈ S, signedBit x a) ^ 2 / (S.card : ℝ) := by
  rw [signed_sum_eq_counts]
  unfold insertedImbalance
  ring

/-- The mean bound of Lemma 4.2 for a fixed deleted-row table `B`.
This has *no* remaining probabilistic, independence, or orthogonality
hypotheses: the conditioning is expressed by taking the uniform average
on the finite type of its admissible missing rows. -/
theorem conditional_inserted_imbalance_le_one
    (B : RemainingTable n m) [Nonempty (Extension B)]
    (S : Finset (Fin m)) (hS : 0 < S.card)
    (hclosed : PairClosed B S) :
    finiteAverage (Ω := Extension B)
      (fun x => insertedImbalance x.1 S) ≤ 1 := by
  have hEq :
      (fun x : Extension B => insertedImbalance x.1 S) =
      (fun x : Extension B =>
        (∑ a ∈ S, signedBit x.1 a) ^ 2 / (S.card : ℝ)) := by
    funext x
    exact insertedImbalance_eq_signed x.1 S
  rw [hEq]
  exact conditional_signed_imbalance_le_one B S hS hclosed

end GradientKey.RowDeletion
/-!
## Exact conditional mean (strengthening of Lemma 4.2)

The preceding sign-sum argument yields the equality `E[v] = f/s`.
The paper only needs `E[v] ≤ 1`, which follows since `f ≤ s`.
-/

namespace GradientKey.RowDeletion

variable {n m : ℕ}

/-- Exact conditional expectation of the deleted row's imbalance.
The candidate set is required to contain full equality classes of `B`.
This is Lemma 4.2's exact moment computation, without assuming any
probabilistic independence or concentration inequality. -/
theorem conditional_inserted_imbalance_exact
    (B : RemainingTable n m) [Nonempty (Extension B)]
    (S : Finset (Fin m)) (hclosed : PairClosed B S) :
    finiteAverage (Ω := Extension B)
      (fun x => insertedImbalance x.1 S) =
      ((uniqueIn B S).card : ℝ) / (S.card : ℝ) := by
  have hFun :
      (fun x : Extension B => insertedImbalance x.1 S) =
      (fun x : Extension B =>
        (∑ a ∈ uniqueIn B S, signedBit x.1 a) ^ 2 /
          (S.card : ℝ)) := by
    funext x
    rw [insertedImbalance_eq_signed,
      all_signs_eq_unique_signs B x.1 x.2 S hclosed]
  rw [hFun]
  calc
    finiteAverage (fun x : Extension B =>
      (∑ a ∈ uniqueIn B S, signedBit x.1 a) ^ 2 /
        (S.card : ℝ)) =
        finiteAverage (fun x : Extension B =>
          (∑ a ∈ uniqueIn B S, signedBit x.1 a) ^ 2) /
            (S.card : ℝ) := finiteAverage_div _ _
    _ = ((uniqueIn B S).card : ℝ) / (S.card : ℝ) := by
      rw [conditional_unique_signs_second_moment B S]

end GradientKey.RowDeletion
/-!
## Lemma 4.3, mean estimate: finite averaging step

This statement turns the pointwise greedy comparison into
`V_i ≤ n/(n-i)` as soon as each row-deleted imbalance has mean ≤ 1.
The latter is exactly the consequence of Lemma 4.2 established above,
subject to connecting the conditional distribution of a deleted row
with the explicit `Extension B` type.

The proof needs no independence between rows and no tail bound.
-/

namespace GradientKey

variable {Ω : Type*} [Fintype Ω] [Nonempty Ω]

/-- The mean half of Lemma 4.3 from the pointwise greedy comparison
and individual row moment estimates. `active r ω` is the event that row
`r` has not been tested before depth `i` on the sampled path and that
the path still contains a fork. -/
theorem mean_imbalance_from_unused_rows
    (n i : ℕ) (hi : i < n)
    (v : Ω → ℝ) (U : Fin n → Ω → ℝ)
    (active : Fin n → Ω → Prop)
    (hU_nonneg : ∀ r ω, 0 ≤ U r ω)
    (hCompare : ∀ ω,
      v ω ≤ (∑ r : Fin n,
        if active r ω then U r ω else 0) /
          ((n : ℝ) - (i : ℝ)))
    (hRowMean : ∀ r, finiteAverage (U r) ≤ 1) :
    finiteAverage v ≤ (n : ℝ) / ((n : ℝ) - (i : ℝ)) := by
  have hiR : (i : ℝ) < (n : ℝ) := by exact_mod_cast hi
  have hd : 0 < (n : ℝ) - (i : ℝ) := by linarith
  have hPoint : ∀ ω, v ω ≤
      (∑ r : Fin n, U r ω) / ((n : ℝ) - (i : ℝ)) := by
    intro ω
    have hNumerator :
        (∑ r : Fin n, if active r ω then U r ω else 0) ≤
        ∑ r : Fin n, U r ω := by
      apply Finset.sum_le_sum
      intro r _
      by_cases hr : active r ω
      · simp [hr]
      · simpa [hr] using hU_nonneg r ω
    have hQuotient :
        (∑ r : Fin n, if active r ω then U r ω else 0) /
          ((n : ℝ) - (i : ℝ)) ≤
        (∑ r : Fin n, U r ω) /
          ((n : ℝ) - (i : ℝ)) := by
      apply (div_le_div_iff₀ hd hd).2
      exact mul_le_mul_of_nonneg_right hNumerator hd.le
    exact (hCompare ω).trans hQuotient
  have hAveraged := finiteAverage_mono v
    (fun ω => (∑ r : Fin n, U r ω) / ((n : ℝ) - (i : ℝ)))
    hPoint
  have hLinear :
      finiteAverage (fun ω : Ω => ∑ r : Fin n, U r ω) =
        ∑ r : Fin n, finiteAverage (U r) := by
    exact finiteAverage_finset_sum
      (s := (Finset.univ : Finset (Fin n))) (fun r ω => U r ω)
  have hAllRows : (∑ r : Fin n, finiteAverage (U r)) ≤ (n : ℝ) := by
    calc
      (∑ r : Fin n, finiteAverage (U r)) ≤
          ∑ _r : Fin n, (1 : ℝ) := by
            apply Finset.sum_le_sum
            intro r _
            exact hRowMean r
      _ = (n : ℝ) := by simp
  calc
    finiteAverage v ≤
        finiteAverage (fun ω : Ω =>
          (∑ r : Fin n, U r ω) / ((n : ℝ) - (i : ℝ))) :=
      hAveraged
    _ = (∑ r : Fin n, finiteAverage (U r)) /
        ((n : ℝ) - (i : ℝ)) := by
          rw [finiteAverage_div, hLinear]
    _ ≤ (n : ℝ) / ((n : ℝ) - (i : ℝ)) := by
          apply (div_le_div_iff₀ hd hd).2
          exact mul_le_mul_of_nonneg_right hAllRows hd.le

end GradientKey
