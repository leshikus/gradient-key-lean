import Mathlib

/-!
# P8 — Standalone audit of Theorem 4.4 (article Section 4)

Source: `article(9).tex`, Lemmas 4.1 and 4.3 and Theorem 4.4.

This is a standalone, namespace-isolated adaptation of the deterministic
Theorem 4.4 segment of the candidate `GradientKeySection4.lean`, audited against
the source paper.  It does not import the candidate and does not formalize the
probabilistic lemmas; the ONLY mathematical inputs are their precise
expectation/recurrence, tail, probability and imbalance bounds.

Status: NOT COMPILED (no Lean/Mathlib toolchain available).  Every declaration
is a candidate proof script until `lake env lean P8_Theorem44.lean` succeeds.

No `sorry`, `admit`, `axiom`, or unsafe definitions appear in this file.
-/

noncomputable section

namespace P8Theorem44

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
### Independent unrolling check

Multiplying the Lemma 4.1 recurrence by `2^(h+1)` gives a telescoping
identity.  This proof is independent of the weighted-sum induction below,
and exposes why the coefficient of `V_i - p_i` is exactly `2^(i-h)`.
-/

private lemma scaled_recurrence_identity
    (m : ℕ) (e p V : ℕ → ℝ)
    (hInit : e 0 = (m : ℝ) - 1)
    (hRec : ∀ i, e (i + 1) = (e i - p i + V i) / 2) :
    ∀ h, (2 : ℝ) ^ h * e h =
      (m : ℝ) - 1 +
        ∑ i ∈ Finset.range h, (2 : ℝ) ^ i * (V i - p i) := by
  intro h
  induction h with
  | zero => simp [hInit]
  | succ h ih =>
      calc
        (2 : ℝ) ^ (h + 1) * e (h + 1) =
            (2 : ℝ) ^ h * e h + (2 : ℝ) ^ h * (V h - p h) := by
              rw [pow_succ, hRec h]
              ring
        _ = ((m : ℝ) - 1 +
            ∑ i ∈ Finset.range h, (2 : ℝ) ^ i * (V i - p i)) +
            (2 : ℝ) ^ h * (V h - p h) := by rw [ih]
        _ = (m : ℝ) - 1 +
            ∑ i ∈ Finset.range (h + 1),
              (2 : ℝ) ^ i * (V i - p i) := by
              rw [Finset.sum_range_succ]
              ring

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
    have hs := scaled_recurrence_identity m e p V hInit hRec h
    have hp : (2 : ℝ) ^ h ≠ 0 := by positivity
    have hShift :
        (∑ i ∈ Finset.range h, weight h i * (V i - p i)) =
          (∑ i ∈ Finset.range h, (2 : ℝ) ^ i * (V i - p i)) /
            (2 : ℝ) ^ h := by
      rw [Finset.sum_div]
      apply Finset.sum_congr rfl
      intro i hi
      unfold weight
      ring
    calc
      e h = ((2 : ℝ) ^ h * e h) / (2 : ℝ) ^ h := by
        field_simp [hp]
      _ = ((m : ℝ) - 1 +
            ∑ i ∈ Finset.range h, (2 : ℝ) ^ i * (V i - p i)) /
            (2 : ℝ) ^ h := by rw [hs]
      _ = ((m : ℝ) - 1) / (2 : ℝ) ^ h +
            ∑ i ∈ Finset.range h, weight h i * (V i - p i) := by
              rw [add_div, ← hShift]
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


end P8Theorem44
