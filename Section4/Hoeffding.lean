import P5_InsertedRowTail

/-!
# The tail bound of Lemma 4.2

For a deleted-row table `B` with an admissible inserted row, a nonempty
pair-closed set `S` and `z > 0`, the number of admissible rows `x` with
`v_x(S) > z` is at most `2 e^{-z/2} |Extension B|`.

Proof: `v_x(S) = Y(x)²/s` with `Y` the signed sum over the `f` unique columns
of `S` (pairs cancel); P5 gives `∑_x e^{tY} = |Extension B| cosh(t)^f`;
`cosh t ≤ e^{t²/2}` and Chernoff's bound with `t = a/f` give
`|{|Y| > a}| ≤ 2 e^{-a²/(2f)} |Extension B|`; take `a² = zs` and use `f ≤ s`.
For `f = 0` the imbalance is identically `0`.
-/

noncomputable section

namespace GradientKey.RowDeletion

open Finset

/-- One-sided Chernoff bound in counting form. -/
theorem chernoff_count {Ω : Type*} [Fintype Ω] (Y : Ω → ℝ) (N f a : ℝ)
    (hf : 0 < f) (ha : 0 ≤ a)
    (hmgf : ∀ t : ℝ, (∑ ω, Real.exp (t * Y ω)) ≤ N * Real.exp (f * t ^ 2 / 2)) :
    ((Finset.univ.filter (fun ω => a < Y ω)).card : ℝ) ≤
      N * Real.exp (-(a ^ 2) / (2 * f)) := by
  classical
  set t : ℝ := a / f
  have ht : 0 ≤ t := div_nonneg ha hf.le
  have hlow : ((Finset.univ.filter (fun ω => a < Y ω)).card : ℝ) * Real.exp (t * a) ≤
      ∑ ω, Real.exp (t * Y ω) := by
    calc ((Finset.univ.filter (fun ω => a < Y ω)).card : ℝ) * Real.exp (t * a)
        = ∑ ω ∈ Finset.univ.filter (fun ω => a < Y ω), Real.exp (t * a) := by
          rw [Finset.sum_const, nsmul_eq_mul]
      _ ≤ ∑ ω ∈ Finset.univ.filter (fun ω => a < Y ω), Real.exp (t * Y ω) := by
          apply Finset.sum_le_sum
          intro ω hω
          have hω' : a < Y ω := (Finset.mem_filter.mp hω).2
          exact Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_left hω'.le ht)
      _ ≤ ∑ ω, Real.exp (t * Y ω) :=
          Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset _ _)
            (fun ω _ _ => (Real.exp_pos _).le)
  have hup := (hlow.trans (hmgf t))
  have hexp_pos : 0 < Real.exp (t * a) := Real.exp_pos _
  have hdiv : ((Finset.univ.filter (fun ω => a < Y ω)).card : ℝ) ≤
      N * Real.exp (f * t ^ 2 / 2) / Real.exp (t * a) := (le_div_iff₀ hexp_pos).2 hup
  refine hdiv.trans (le_of_eq ?_)
  rw [mul_div_assoc, ← Real.exp_sub]
  congr 2
  simp only [t]
  field_simp
  ring

/-- Two-sided Chernoff bound in counting form. -/
theorem chernoff_count_abs {Ω : Type*} [Fintype Ω] (Y : Ω → ℝ) (N f a : ℝ)
    (hf : 0 < f) (ha : 0 ≤ a)
    (hmgf : ∀ t : ℝ, (∑ ω, Real.exp (t * Y ω)) ≤ N * Real.exp (f * t ^ 2 / 2)) :
    ((Finset.univ.filter (fun ω => a < |Y ω|)).card : ℝ) ≤
      2 * N * Real.exp (-(a ^ 2) / (2 * f)) := by
  classical
  have hpos := chernoff_count Y N f a hf ha hmgf
  have hneg := chernoff_count (fun ω => -Y ω) N f a hf ha (by
    intro t
    have h := hmgf (-t)
    simp only [neg_mul, mul_neg, neg_sq] at h ⊢
    exact h)
  have hsub : Finset.univ.filter (fun ω => a < |Y ω|) ⊆
      Finset.univ.filter (fun ω => a < Y ω) ∪ Finset.univ.filter (fun ω => a < -Y ω) := by
    intro ω hω
    have h := (Finset.mem_filter.mp hω).2
    rcases lt_abs.mp h with h1 | h1
    · exact Finset.mem_union_left _ (Finset.mem_filter.mpr ⟨Finset.mem_univ _, h1⟩)
    · exact Finset.mem_union_right _ (Finset.mem_filter.mpr ⟨Finset.mem_univ _, h1⟩)
  have hcard := (Finset.card_le_card hsub).trans (Finset.card_union_le _ _)
  have hcardR : ((Finset.univ.filter (fun ω => a < |Y ω|)).card : ℝ) ≤
      ((Finset.univ.filter (fun ω => a < Y ω)).card : ℝ) +
        ((Finset.univ.filter (fun ω => a < -Y ω)).card : ℝ) := by
    exact_mod_cast hcard
  linarith

variable {n m : ℕ}

/-- The exponential moment bound for the unique-column sign sum. -/
theorem unique_sign_mgf_le (B : RemainingTable n m) (S : Finset (Fin m)) (t : ℝ) :
    (∑ x : Extension B,
      Real.exp (t * (∑ a ∈ uniqueIn B S, signedBit x.1 a))) ≤
      (Fintype.card (Extension B) : ℝ) *
        Real.exp (((uniqueIn B S).card : ℝ) * t ^ 2 / 2) := by
  rw [unique_sign_mgf_exact]
  apply mul_le_mul_of_nonneg_left _ (Nat.cast_nonneg _)
  rw [← Real.cosh_eq]
  calc Real.cosh t ^ (uniqueIn B S).card
      ≤ Real.exp (t ^ 2 / 2) ^ (uniqueIn B S).card :=
        pow_le_pow_left₀ (Real.cosh_pos t).le (Real.cosh_le_exp_half_sq t) _
    _ = Real.exp (((uniqueIn B S).card : ℝ) * t ^ 2 / 2) := by
        rw [← Real.exp_nat_mul]
        ring_nf

/-- **Lemma 4.2, tail bound**, for a fixed deleted-row table `B` and a
nonempty pair-closed candidate set `S`: among the admissible inserted rows,
at most a fraction `2 e^{-z/2}` have split imbalance greater than `z`. -/
theorem conditional_inserted_imbalance_tail
    (B : RemainingTable n m) (S : Finset (Fin m)) (hS : 0 < S.card)
    (hclosed : PairClosed B S) (z : ℝ) (hz : 0 < z) :
    ((Finset.univ.filter
        (fun x : Extension B => z < insertedImbalance x.1 S)).card : ℝ) ≤
      2 * Real.exp (-z / 2) * (Fintype.card (Extension B) : ℝ) := by
  classical
  set F := uniqueIn B S
  set N : ℝ := (Fintype.card (Extension B) : ℝ)
  have hsR : (0 : ℝ) < S.card := by exact_mod_cast hS
  have hY : ∀ x : Extension B, insertedImbalance x.1 S =
      (∑ a ∈ F, signedBit x.1 a) ^ 2 / (S.card : ℝ) := by
    intro x
    rw [insertedImbalance_eq_signed, all_signs_eq_unique_signs B x.1 x.2 S hclosed]
  by_cases hf0 : F.card = 0
  · have hempty : Finset.univ.filter
        (fun x : Extension B => z < insertedImbalance x.1 S) = ∅ := by
      apply Finset.filter_false_of_mem
      intro x _
      rw [hY x, Finset.card_eq_zero.mp hf0]
      simp [hz.le]
    rw [hempty]
    simp only [Finset.card_empty, Nat.cast_zero]
    positivity
  have hf : (0 : ℝ) < F.card := by exact_mod_cast Nat.pos_of_ne_zero hf0
  have hfs : (F.card : ℝ) ≤ S.card := by
    exact_mod_cast Finset.card_le_card (Finset.filter_subset _ S)
  set a : ℝ := Real.sqrt (z * S.card)
  have ha : 0 ≤ a := Real.sqrt_nonneg _
  have ha2 : a ^ 2 = z * S.card := Real.sq_sqrt (by positivity)
  have hsub : Finset.univ.filter (fun x : Extension B => z < insertedImbalance x.1 S) ⊆
      Finset.univ.filter (fun x : Extension B => a < |∑ b ∈ F, signedBit x.1 b|) := by
    intro x hx
    have h := (Finset.mem_filter.mp hx).2
    rw [hY x, lt_div_iff₀ hsR] at h
    refine Finset.mem_filter.mpr ⟨Finset.mem_univ _, ?_⟩
    by_contra hle
    push Not at hle
    have h2 : (∑ b ∈ F, signedBit x.1 b) ^ 2 ≤ a ^ 2 := by
      rw [← sq_abs]
      exact pow_le_pow_left₀ (abs_nonneg _) hle 2
    linarith
  have hch := chernoff_count_abs (fun x : Extension B => ∑ b ∈ F, signedBit x.1 b)
    N F.card a hf ha (fun t => unique_sign_mgf_le B S t)
  have hcard : ((Finset.univ.filter
      (fun x : Extension B => z < insertedImbalance x.1 S)).card : ℝ) ≤
      ((Finset.univ.filter
        (fun x : Extension B => a < |∑ b ∈ F, signedBit x.1 b|)).card : ℝ) := by
    exact_mod_cast Finset.card_le_card hsub
  have hexp : Real.exp (-(a ^ 2) / (2 * F.card)) ≤ Real.exp (-z / 2) := by
    apply Real.exp_le_exp.mpr
    rw [ha2, div_le_div_iff₀ (by positivity) (by norm_num)]
    nlinarith
  have hN : 0 ≤ N := Nat.cast_nonneg _
  calc _ ≤ _ := hcard
    _ ≤ 2 * N * Real.exp (-(a ^ 2) / (2 * F.card)) := hch
    _ ≤ 2 * N * Real.exp (-z / 2) := by
        apply mul_le_mul_of_nonneg_left hexp; positivity
    _ = 2 * Real.exp (-z / 2) * N := by ring

end GradientKey.RowDeletion
