import PathGroup

/-!
# Proposition 3.2: the row counts are `W(M)` and `V_j(M)`

For a chain `s`, integer partitions `λ_j` of the cell sizes and a schedule `ρ`, the count `cntU` of
admissible assignments of row `i` equals `W(M_i)` if `i` is not a tested row and `V_j(M_{ρ(j)})` if
`i = ρ(j)`, with `M_i = {k : ρ(k) < i}` (`cntU_W`, `cntU_V`). At depths after `j` the tested row
`ρ(j)` is constant on the candidate set, so its quality there is `0 < q`; these conditions hold
automatically and do not appear in `V_j`.
-/

noncomputable section

namespace GradientKey.Concrete

open Finset Classical

variable {n m : ℕ}

section chain

variable (s : PathChain n m)

theorem chain_step_lt (j : Fin (pathChainDepth s)) :
    (pathChainSizes s j.succ).val < (pathChainSizes s j.castSucc).val := s.2.2.2 j

theorem chain_last_ge : 2 ≤ (pathChainSizes s (Fin.last _)).val := s.2.2.1

theorem chain_zero : (pathChainSizes s 0).val = m := s.2.1

/-- The sizes of a chain are at least the last one. -/
theorem chain_ge_last (i : Fin (pathChainDepth s + 1)) :
    (pathChainSizes s (Fin.last _)).val ≤ (pathChainSizes s i).val := by
  induction i using Fin.reverseInduction with
  | last => exact le_rfl
  | cast k ih => exact ih.trans (chain_step_lt s k).le

theorem chain_two_le (i : Fin (pathChainDepth s + 1)) : 2 ≤ (pathChainSizes s i).val :=
  (chain_last_ge s).trans (chain_ge_last s i)

theorem chain_le_m (i : Fin (pathChainDepth s + 1)) : (pathChainSizes s i).val ≤ m := by
  have := (pathChainSizes s i).isLt
  omega

theorem pathCellSize_castSucc (k : Fin (pathChainDepth s)) :
    pathCellSize s k.castSucc = (pathChainSizes s k.castSucc).val - (pathChainSizes s k.succ).val := by
  unfold pathCellSize
  rw [dif_pos (by simp)]
  rfl

theorem pathCellSize_last :
    pathCellSize s (Fin.last _) = (pathChainSizes s (Fin.last _)).val := by
  unfold pathCellSize
  rw [dif_neg (by simp)]

theorem pathCellSize_le (j : Fin (pathChainDepth s + 1)) : pathCellSize s j ≤ m := by
  unfold pathCellSize
  split_ifs
  · have := chain_le_m s j; omega
  · exact chain_le_m s j

theorem pathQuality_pos (k : Fin (pathChainDepth s)) : 1 ≤ pathQuality s k := by
  unfold pathQuality
  rw [pathCellSize_castSucc]
  have h1 := chain_step_lt s k
  have h2 := chain_two_le s k.succ
  omega

/-- The cells `j ≥ i` make up `S_i`: `∑_{j ≥ i} a_j = s_i`. -/
theorem chain_sum_cells (i : Fin (pathChainDepth s + 1)) :
    ∑ j : Fin (pathChainDepth s + 1), (if i.val ≤ j.val then pathCellSize s j else 0) =
      (pathChainSizes s i).val := by
  induction i using Fin.reverseInduction with
  | last =>
    rw [sum_eq_single (Fin.last _)]
    · rw [if_pos le_rfl, pathCellSize_last]
    · intro j _ hj
      rw [if_neg]
      intro h
      exact hj (Fin.ext (by have := j.isLt; simp at h ⊢; omega))
    · simp
  | cast k ih =>
    have hpt : ∀ j : Fin (pathChainDepth s + 1),
        (if (k.castSucc : Fin _).val ≤ j.val then pathCellSize s j else 0) =
          (if k.castSucc = j then pathCellSize s j else 0) +
            (if (k.succ : Fin _).val ≤ j.val then pathCellSize s j else 0) := by
      intro j
      by_cases h1 : k.castSucc = j
      · subst h1; simp
      · have : (k.castSucc : Fin _).val ≠ j.val := fun h => h1 (Fin.ext h)
        simp only [Fin.coe_castSucc, Fin.val_succ] at this ⊢
        rw [if_neg h1, zero_add]
        by_cases h2 : k.val ≤ j.val
        · rw [if_pos h2, if_pos (by omega)]
        · rw [if_neg h2, if_neg (by omega)]
    rw [sum_congr rfl (fun j _ => hpt j), sum_add_distrib, sum_ite_eq, if_pos (mem_univ _), ih,
      pathCellSize_castSucc]
    have := chain_step_lt s k
    omega

end chain

section blocks

variable {s : PathChain n m} (parts : PathPartitionTypes s)

/-- The blocks of the cells `j ≥ i` have total size `s_i`. -/
theorem blocks_total (i : Fin (pathChainDepth s + 1)) :
    ∑ b : PathBlocks s parts, (if i.val ≤ b.1.val then b.2.1.val else 0) = (pathChainSizes s i).val := by
  rw [← chain_sum_cells s i]
  rw [Fintype.sum_sigma]
  apply sum_congr rfl
  intro j _
  rw [Fintype.sum_sigma]
  split_ifs with h
  · refine Eq.trans ?_ (parts j).2.2
    apply sum_congr rfl
    intro v _
    simp only [sum_const, card_univ, Fintype.card_fin, smul_eq_mul]
    ring
  · simp

/-- If the bits are constant on the cells `≥ i`, the quality on `S_i` is `0`. -/
theorem quality_const (i : Fin (pathChainDepth s + 1)) (bits : PathAssignment s parts) (bb : Bool)
    (h : ∀ b : PathBlocks s parts, i.val ≤ b.1.val → bits b = bb) :
    pathRowQuality s parts bits i = 0 := by
  unfold pathRowQuality pathOnes
  have hT := blocks_total parts i
  cases bb
  · have : ∑ b : PathBlocks s parts, (if i.val ≤ b.1.val ∧ bits b = true then b.2.1.val else 0) = 0 := by
      apply sum_eq_zero
      intro b _
      rw [if_neg]
      rintro ⟨h1, h2⟩
      rw [h b h1] at h2
      exact Bool.false_ne_true h2
    rw [this]; simp
  · have : ∑ b : PathBlocks s parts, (if i.val ≤ b.1.val ∧ bits b = true then b.2.1.val else 0) =
        (pathChainSizes s i).val := by
      rw [← hT]
      apply sum_congr rfl
      intro b _
      by_cases h1 : i.val ≤ b.1.val
      · rw [if_pos ⟨h1, h b h1⟩, if_pos h1]
      · rw [if_neg (fun h' => h1 h'.1), if_neg h1]
    rw [this]; simp

end blocks

section conversion

variable {s : PathChain n m} (parts : PathPartitionTypes s)
  (sz : Fin (pathChainDepth s + 1) → ℕ) (q : Fin (pathChainDepth s) → ℕ)

theorem blkQual_eq (hsz : ∀ i, sz i = (pathChainSizes s i).val) (bits : PathAssignment s parts)
    (i : Fin (pathChainDepth s + 1)) :
    blkQual (fun b : PathBlocks s parts => b.2.1.val) (fun b => b.1) sz bits i =
      pathRowQuality s parts bits i := by
  unfold blkQual pathRowQuality blkOnes pathOnes
  rw [hsz]
  rfl

theorem cntU_card (rho : Fin (pathChainDepth s) ↪ Fin n) (i : Fin n) :
    cntU (m + 1) (fun j v => ((parts j).1 v).val) sz q rho i =
      (univ.filter (fun bits : PathAssignment s parts =>
        blkAdm (fun b : PathBlocks s parts => b.2.1.val) (fun b => b.1) sz q rho i bits)).card := by
  unfold cntU
  rw [Fintype.card_subtype]

/-- **Unscheduled rows give `W(M_i)`.** -/
theorem cntU_W (hsz : ∀ i, sz i = (pathChainSizes s i).val) (hq : ∀ j, q j = pathQuality s j)
    (rho : Fin (pathChainDepth s) ↪ Fin n) (i : Fin n) (hi : ∀ j, rho j ≠ i) :
    cntU (m + 1) (fun j v => ((parts j).1 v).val) sz q rho i = pathW s parts (pathBefore s rho i) := by
  rw [cntU_card]
  unfold pathW
  congr 1
  apply filter_congr
  intro bits _
  unfold blkAdm pathMeetsQuality pathBefore
  apply forall_congr'
  intro j
  rw [blkQual_eq parts sz hsz, hq]
  have hne := hi j
  simp only [hne, IsEmpty.forall_iff, ne_eq, not_false_eq_true, forall_const, true_and, mem_filter,
    mem_univ]
  rcases lt_trichotomy i (rho j) with h | h | h
  · rw [if_pos h, if_neg (not_lt.mpr h.le)]
  · exact absurd h.symm hne
  · rw [if_neg (not_lt.mpr h.le), if_pos h]

/-- **The row `ρ(j₁)` gives `V_{j₁}(M_{ρ(j₁)})`.** -/
theorem cntU_V (hsz : ∀ i, sz i = (pathChainSizes s i).val) (hq : ∀ j, q j = pathQuality s j)
    (rho : Fin (pathChainDepth s) ↪ Fin n) (j₁ : Fin (pathChainDepth s)) :
    cntU (m + 1) (fun j v => ((parts j).1 v).val) sz q rho (rho j₁) =
      pathV s parts j₁ (pathBefore s rho (rho j₁)) := by
  rw [cntU_card]
  unfold pathV
  congr 1
  apply filter_congr
  intro bits _
  have hsplit : ∀ j : Fin (pathChainDepth s), (∃ bb : Bool, ∀ b : PathBlocks s parts,
      (b.1 = j.castSucc → bits b = !bb) ∧ (j.castSucc < b.1 → bits b = bb)) ↔
      (∃ bb : Bool, ∀ b : PathBlocks s parts,
        (b.1.val = j.val → bits b = !bb) ∧ (j.val < b.1.val → bits b = bb)) := by
    intro j
    simp only [Fin.ext_iff, Fin.lt_iff_val_lt_val, Fin.coe_castSucc]
  have hmeet : ∀ k : Fin (pathChainDepth s), rho k ≠ rho j₁ →
      ((if rho j₁ < rho k then
          blkQual (fun b : PathBlocks s parts => b.2.1.val) (fun b => b.1) sz bits k.castSucc < q k
        else blkQual (fun b : PathBlocks s parts => b.2.1.val) (fun b => b.1) sz bits k.castSucc ≤ q k) ↔
        pathMeetsQuality s parts bits (pathBefore s rho (rho j₁)) k) := by
    intro k hk
    unfold pathMeetsQuality pathBefore
    rw [blkQual_eq parts sz hsz, hq]
    simp only [mem_filter, mem_univ, true_and]
    rcases lt_trichotomy (rho j₁) (rho k) with h | h | h
    · rw [if_pos h, if_neg (not_lt.mpr h.le)]
    · exact absurd h.symm hk
    · rw [if_neg (not_lt.mpr h.le), if_pos h]
  unfold blkAdm
  constructor
  · intro h
    refine ⟨(hsplit j₁).mp ((h j₁).1 rfl), ?_⟩
    intro k hk
    have hne : rho k ≠ rho j₁ := fun he => by
      have := rho.injective he
      rw [this] at hk
      exact lt_irrefl _ hk
    exact (hmeet k hne).mp ((h k).2 hne)
  · rintro ⟨hs, hb⟩
    intro k
    by_cases hkj : k = j₁
    · subst hkj
      exact ⟨fun _ => (hsplit k).mpr hs, fun h => absurd rfl h⟩
    · have hne : rho k ≠ rho j₁ := fun he => hkj (rho.injective he)
      refine ⟨fun he => absurd he hne, fun _ => ?_⟩
      rcases lt_or_gt_of_ne (Fin.val_ne_of_ne hkj) with hlt | hgt
      · exact (hmeet k hne).mpr (hb k hlt)
      · obtain ⟨bb, hbb⟩ := hs
        have h0 : pathRowQuality s parts bits k.castSucc = 0 :=
          quality_const parts k.castSucc bits bb (fun b hb' => (hbb b).2 (by simp at hb'; omega))
        rw [blkQual_eq parts sz hsz, h0, hq]
        have := pathQuality_pos s k
        split_ifs <;> omega

end conversion

end GradientKey.Concrete
