import NearBall

/-!
# The complete tree is optimal

`cdepth s` is the least total depth of a tree of splitting forks with `s` leaves. Used in Proposition 3.3:
`B_k ≥ 0` (cost is at least `C(m)`), `B_M = 0` (balanced forks), `m ≤ 3` (every fork is balanced), and the comb
that gives `B_{m-1} > 0` for `m ≥ 4`.
-/

noncomputable section

namespace GradientKey.Concrete

open Finset

variable {n m : ℕ}

theorem cdepth_two : cdepth 2 = 2 := by
  rw [cdepth_eq 1 2 (by norm_num) (by norm_num)]; norm_num

/-- `cdepth (s+1) = cdepth s + ⌊log₂ s⌋ + 2` for `s ≥ 1`. -/
theorem cdepth_succ (s : ℕ) (hs : 1 ≤ s) : cdepth (s + 1) = cdepth s + (Nat.log 2 s + 2) := by
  set h := Nat.log 2 s
  have h1 : 2 ^ h ≤ s := Nat.pow_log_le_self 2 (by omega)
  have h2 : s < 2 ^ (h + 1) := Nat.lt_pow_succ_log_self (by norm_num) s
  rw [cdepth_eq h s h1 h2.le, cdepth_eq h (s + 1) (by omega) h2]
  have : 2 ^ (h + 1) ≤ s * (h + 2) := by
    calc 2 ^ (h + 1) = 2 * 2 ^ h := by ring
      _ ≤ 2 * s := by omega
      _ ≤ s * (h + 2) := by nlinarith
  have : s * (h + 2) ≤ (s + 1) * (h + 2) := Nat.mul_le_mul_right _ (by omega)
  zify [*, le_trans ‹2 ^ (h + 1) ≤ s * (h + 2)› this]
  ring

theorem cdepth_add_sum (x : ℕ) (hx : 1 ≤ x) (d : ℕ) :
    cdepth (x + d) = cdepth x + ∑ i ∈ range d, (Nat.log 2 (x + i) + 2) := by
  induction d with
  | zero => simp
  | succ d ih => rw [← add_assoc, cdepth_succ _ (by omega), ih, sum_range_succ, add_assoc]

/-- The balanced split: `cdepth s = s + cdepth ⌊s/2⌋ + cdepth ⌈s/2⌉` for `s ≥ 2`. -/
theorem cdepth_balanced (s : ℕ) (hs : 2 ≤ s) :
    cdepth s = s + cdepth (s / 2) + cdepth (s - s / 2) := by
  set t := Nat.log 2 s
  have h1 : 2 ^ t ≤ s := Nat.pow_log_le_self 2 (by omega)
  have h2 : s < 2 ^ (t + 1) := Nat.lt_pow_succ_log_self (by norm_num) s
  have ht : 1 ≤ t := Nat.le_log_of_pow_le (by norm_num) (by simpa using hs)
  have hp : 2 ^ t = 2 * 2 ^ (t - 1) := two_pow_pred t ht
  have hp' : 2 ^ (t + 1) = 2 * 2 ^ t := by ring
  have := cdepth_add (t - 1) (s / 2) (s - s / 2) (by omega) (by rw [Nat.sub_add_cancel ht]; omega)
    (by omega) (by rw [Nat.sub_add_cancel ht]; omega)
  rw [Nat.add_sub_cancel' (Nat.div_le_self s 2)] at this
  omega

/-- Convexity: a split `a + b = s` costs at least the balanced split. -/
theorem cdepth_split_le (a b : ℕ) (ha : 1 ≤ a) (hb : 1 ≤ b) :
    cdepth (a + b) ≤ a + b + cdepth a + cdepth b := by
  wlog hab : a ≤ b generalizing a b
  · have := this b a hb ha (by omega); rw [add_comm a b]; omega
  rw [cdepth_balanced (a + b) (by omega)]
  set h1 := (a + b) / 2
  set h2 := (a + b) - (a + b) / 2
  have e1 : a ≤ h1 := by omega
  have e2 : h1 ≤ h2 := by omega
  have e3 : h2 ≤ b := by omega
  set d := h1 - a
  have hd : b = h2 + d := by omega
  have hh1 : h1 = a + d := by omega
  have : cdepth h1 + cdepth h2 ≤ cdepth a + cdepth b := by
    rw [hd, hh1, cdepth_add_sum a ha d, cdepth_add_sum h2 (by omega) d]
    have : ∑ i ∈ range d, (Nat.log 2 (a + i) + 2) ≤ ∑ i ∈ range d, (Nat.log 2 (h2 + i) + 2) :=
      sum_le_sum (fun i _ => by have := Nat.log_mono_right (b := 2) (show a + i ≤ h2 + i by omega); omega)
    omega
  omega

/-- Every greedy tree on a set of distinct columns has total depth at least `cdepth |S|`. -/
theorem cdepth_le_totalDepth (A : Table n m) (hA : DistinctColumns A) (hn : 0 < n) :
    ∀ S : Finset (Fin m), cdepth S.card ≤ totalDepth A hn S := by
  intro S
  induction h : S.card using Nat.strong_induction_on generalizing S with
  | _ s ih =>
  by_cases hs : s ≤ 1
  · interval_cases s <;> simp [cdepth]
  have hS2 : 2 ≤ S.card := by omega
  rw [totalDepth_fork A hA hn S hS2]
  have hadd := child_card_add A hn S
  have l1 := child_card_lt A hA hn S hS2 true
  have l0 := child_card_lt A hA hn S hS2 false
  have i1 := ih _ (by omega) (child A hn S true) rfl
  have i0 := ih _ (by omega) (child A hn S false) rfl
  have := cdepth_split_le (child A hn S true).card (child A hn S false).card (by omega) (by omega)
  rw [hadd, h] at this
  omega

theorem quality_le_half (A : Table n m) (S : Finset (Fin m)) (r : Fin n) :
    quality A S r ≤ S.card / 2 := by
  have := slice_card_add A S r
  rw [quality_eq]
  have := min_le_left (slice A S r true).card (slice A S r false).card
  have := min_le_right (slice A S r true).card (slice A S r false).card
  omega

/-- If every set of columns has a row splitting it as evenly as possible, `G` builds the complete tree. -/
theorem totalDepth_eq_cdepth_of_balanced (A : Table n m) (hA : DistinctColumns A) (hn : 0 < n)
    (hbal : ∀ S : Finset (Fin m), ∃ r, quality A S r = S.card / 2) :
    ∀ S : Finset (Fin m), totalDepth A hn S = cdepth S.card := by
  intro S
  induction h : S.card using Nat.strong_induction_on generalizing S with
  | _ s ih =>
  by_cases hs : s ≤ 1
  · rw [totalDepth_le_one A hn S (by omega)]; interval_cases s <;> simp [cdepth]
  have hS2 : 2 ≤ S.card := by omega
  obtain ⟨r, hr⟩ := hbal S
  have hq := p1_greedy_quality_max A S hn r
  have hq' := quality_le_half A S (greedyRow A S hn)
  have hadd := child_card_add A hn S
  have hmin : min (child A hn S true).card (child A hn S false).card = s / 2 := by
    have := quality_eq A S (greedyRow A S hn); rw [← h]; exact (this.symm.trans (by omega))
  rw [totalDepth_fork A hA hn S hS2, ih _ (by omega) (child A hn S true) rfl,
    ih _ (by omega) (child A hn S false) rfl, h, cdepth_balanced s (by omega)]
  rw [h] at hadd
  rcases min_choice (child A hn S true).card (child A hn S false).card with hc | hc <;> rw [hc] at hmin
  · rw [hmin, show (child A hn S false).card = s - s / 2 by omega]
  · rw [hmin, show (child A hn S true).card = s - s / 2 by omega]; ring

/-- On at most three columns every tree of splitting forks is complete. -/
theorem totalDepth_le_three (A : Table n m) (hA : DistinctColumns A) (hn : 0 < n)
    (S : Finset (Fin m)) (hS : S.card ≤ 3) : totalDepth A hn S = cdepth S.card := by
  induction h : S.card using Nat.strong_induction_on generalizing S with
  | _ s ih =>
  by_cases hs : s ≤ 1
  · rw [totalDepth_le_one A hn S (by omega)]; interval_cases s <;> simp [cdepth]
  have hS2 : 2 ≤ S.card := by omega
  have hadd := child_card_add A hn S
  have l1 := child_card_lt A hA hn S hS2 true
  have l0 := child_card_lt A hA hn S hS2 false
  have n1 : 1 ≤ (child A hn S true).card := by omega
  have n0 : 1 ≤ (child A hn S false).card := by omega
  rw [totalDepth_fork A hA hn S hS2, ih _ (by omega) _ (by omega) rfl, ih _ (by omega) _ (by omega) rfl]
  rw [h] at hadd
  have hs3 : s = 2 ∨ s = 3 := by omega
  rcases hs3 with rfl | rfl
  · rw [show (child A hn S true).card = 1 by omega, show (child A hn S false).card = 1 by omega,
      cdepth_one, cdepth_two, h]
  · rcases (show (child A hn S true).card = 1 ∨ (child A hn S true).card = 2 by omega) with e | e
    · rw [e, show (child A hn S false).card = 2 by omega, cdepth_three, cdepth_one, cdepth_two, h]
    · rw [e, show (child A hn S false).card = 1 by omega, cdepth_three, cdepth_one, cdepth_two, h]

/-- The greedy row is the first row of largest quality. -/
theorem greedyRow_eq (A : Table n m) (S : Finset (Fin m)) (hn : 0 < n) (g : Fin n)
    (hmax : ∀ r, quality A S r ≤ quality A S g) (hfirst : ∀ r, r < g → quality A S r < quality A S g) :
    greedyRow A S hn = g := by
  have h1 := p1_greedy_quality_max A S hn g
  have h2 := hmax (greedyRow A S hn)
  have h3 := p1_greedy_first_max A S hn g (by omega)
  rcases lt_or_eq_of_le h3 with hlt | heq
  · have := hfirst _ hlt; omega
  · exact heq

/-! ## The comb: rows singling out columns `1, …, m-1` -/

/-- Row `i` is `1` exactly on column `i + 1`. -/
def combTable (m : ℕ) : Table (m - 1) m := fun i k => decide (k.val = i.val + 1)

theorem combTable_distinct (m : ℕ) : DistinctColumns (combTable m) := by
  intro j k h
  by_contra hjk
  wlog hlt : j.val < k.val generalizing j k
  · exact this h.symm (Ne.symm hjk) (by have := Fin.val_ne_of_ne hjk; omega)
  have hk : 1 ≤ k.val := by omega
  have := congrFun h ⟨k.val - 1, by omega⟩
  simp [combTable] at this
  omega

/-- `S_t = {0} ∪ {k : t < k}`. -/
def combSet (m t : ℕ) : Finset (Fin m) := univ.filter (fun k : Fin m => k.val = 0 ∨ t < k.val)

theorem combSet_card (m t : ℕ) (hm : 1 ≤ m) (ht : t < m) : (combSet m t).card = m - t := by
  have e : combSet m t = insert ⟨0, by omega⟩ ((univ : Finset (Fin m)).filter (fun k => t < k.val)) := by
    ext k; simp [combSet, Fin.ext_iff]
  rw [e, card_insert_of_notMem (by simp)]
  have : ((univ : Finset (Fin m)).filter (fun k => t < k.val)).card = m - 1 - t := by
    rw [← card_map Fin.valEmbedding]
    have : ((univ : Finset (Fin m)).filter (fun k => t < k.val)).map Fin.valEmbedding =
        Finset.Ioo t m := by
      ext x; simp only [mem_map, mem_filter, mem_univ, true_and, Fin.valEmbedding_apply, mem_Ioo]
      constructor
      · rintro ⟨k, hk, rfl⟩; exact ⟨hk, k.2⟩
      · rintro ⟨h1, h2⟩; exact ⟨⟨x, h2⟩, h1, rfl⟩
    rw [this, Nat.card_Ioo]; omega
  omega

theorem combTable_ones (m t : ℕ) (r : Fin (m - 1)) :
    ones (combTable m) (combSet m t) r = if t ≤ r.val then 1 else 0 := by
  unfold ones
  have : (combSet m t).filter (fun k => combTable m r k = true) =
      if t ≤ r.val then {⟨r.val + 1, by omega⟩} else ∅ := by
    ext k
    simp only [combSet, combTable, mem_filter, mem_univ, true_and, decide_eq_true_eq]
    split_ifs with h
    · simp only [mem_singleton, Fin.ext_iff]; omega
    · simp only [notMem_empty, iff_false]; omega
  rw [this]; split_ifs <;> simp

theorem combTable_quality (m t : ℕ) (hm : 2 ≤ m) (ht : t + 2 ≤ m) (r : Fin (m - 1)) :
    quality (combTable m) (combSet m t) r = if t ≤ r.val then 1 else 0 := by
  have h1 := combTable_ones m t r
  have hc := combSet_card m t (by omega) (by omega)
  have hadd := slice_card_add (combTable m) (combSet m t) r
  unfold quality
  change min (slice _ _ r true).card (slice _ _ r false).card = _
  change (slice _ _ r true).card = _ at h1
  split_ifs at h1 ⊢ <;> omega

theorem comb_greedy (m t : ℕ) (hm : 2 ≤ m) (ht : t + 2 ≤ m) (hn : 0 < m - 1) :
    greedyRow (combTable m) (combSet m t) hn = ⟨t, by omega⟩ := by
  apply greedyRow_eq
  · intro r; rw [combTable_quality m t hm ht, combTable_quality m t hm ht]; split_ifs <;> simp_all
  · intro r hr
    rw [combTable_quality m t hm ht, combTable_quality m t hm ht]
    have : ¬ t ≤ r.val := by have := Fin.lt_def.mp hr; simp at this; omega
    simp [this]

theorem comb_children (m t : ℕ) (hm : 2 ≤ m) (ht : t + 2 ≤ m) (hn : 0 < m - 1) :
    child (combTable m) hn (combSet m t) false = combSet m (t + 1) ∧
      (child (combTable m) hn (combSet m t) true).card = 1 := by
  have hg := comb_greedy m t hm ht hn
  constructor
  · ext k
    unfold child
    rw [hg]
    simp only [combSet, combTable, mem_filter, mem_univ, true_and, decide_eq_false_iff_not]
    omega
  · have := combTable_ones m t ⟨t, by omega⟩
    simp only [le_refl, if_true] at this
    unfold ones at this
    unfold child
    rw [hg]
    exact this

theorem comb_totalDepth (m : ℕ) (hm : 2 ≤ m) (hn : 0 < m - 1) :
    ∀ u, u + 1 ≤ m → totalDepth (combTable m) hn (combSet m (m - 1 - u)) =
      ∑ i ∈ range u, (i + 2) := by
  intro u
  induction u with
  | zero =>
    intro _
    rw [totalDepth_le_one _ hn _ (by rw [combSet_card m _ (by omega) (by omega)]; omega)]
    simp
  | succ u ih =>
    intro hu
    set t := m - 1 - (u + 1)
    have ht : t + 2 ≤ m := by omega
    have hc := combSet_card m t (by omega) (by omega)
    obtain ⟨hf, ht1⟩ := comb_children m t hm ht hn
    rw [totalDepth_fork_side (combTable m) (combTable_distinct m) hn _ (by omega) true]
    simp only [Bool.not_true]
    rw [hf, totalDepth_le_one _ hn _ ht1.le, show t + 1 = m - 1 - u by omega, ih (by omega), hc,
      sum_range_succ]
    omega

/-- The comb has total depth `2 + 3 + ⋯ + m`, more than `cdepth m` for `m ≥ 4`. -/
theorem comb_excess (m : ℕ) (hm : 4 ≤ m) (hn : 0 < m - 1) :
    cdepth m < totalDepth (combTable m) hn univ := by
  have h := comb_totalDepth m (by omega) hn (m - 1) (by omega)
  rw [show m - 1 - (m - 1) = 0 by omega] at h
  have hu : combSet m 0 = univ := by ext k; simp [combSet]; omega
  rw [hu] at h
  rw [h]
  have hc := cdepth_add_sum 1 le_rfl (m - 1)
  rw [show 1 + (m - 1) = m by omega, cdepth_one, zero_add] at hc
  rw [hc]
  apply sum_lt_sum
  · intro i _
    have := Nat.log_lt_self 2 (show 1 + i ≠ 0 by omega)
    omega
  · refine ⟨2, mem_range.mpr (by omega), ?_⟩
    have : Nat.log 2 3 = 1 := by
      rw [Nat.log_eq_iff (by norm_num)]; norm_num
    rw [show 1 + 2 = 3 by rfl, this]; norm_num

end GradientKey.Concrete
