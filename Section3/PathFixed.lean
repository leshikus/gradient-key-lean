import PathWV

/-!
# Proposition 3.1: the count for one family of candidate sets

Fix a chain `s` and a column `j₀`. A family of candidate sets for `s` is `S₀ ⊇ … ⊇ S_d` with `S₀` the set
of all columns, `|S_i| = s_i` and `j₀ ∈ S_d` (`pathFams`). For each such family, the number of valid
tables in which the path of `j₀` has the candidate sets `S₀,…,S_d` is
`∑_{λ_0,…,λ_d} (∏_j c(λ_j)) F_n` (`card_path_fixed`): it depends only on `s`.
-/

noncomputable section

namespace GradientKey.Concrete

open Finset Classical

variable {n m : ℕ}

/-- The families of candidate sets of the chain `s` containing the column `j₀`. -/
def pathFams (s : PathChain n m) (j₀ : Fin m) :
    Finset (Fin (pathChainDepth s + 1) → Finset (Fin m)) :=
  univ.filter (fun S => S 0 = univ ∧ (∀ k : Fin (pathChainDepth s), S k.succ ⊆ S k.castSucc) ∧
    j₀ ∈ S (Fin.last _) ∧ ∀ i, (S i).card = (pathChainSizes s i).val)

/-- The sum over the integer partitions of the cells in Proposition 3.1. -/
def pathPartSum (s : PathChain n m) : ℚ :=
  ∑ parts : PathPartitionTypes s, (∏ j, pathCoeff (parts j)) * (pathF s parts : ℚ)

theorem mem_pathFams {s : PathChain n m} {j₀ : Fin m} {S : Fin (pathChainDepth s + 1) → Finset (Fin m)} :
    S ∈ pathFams s j₀ ↔ S 0 = univ ∧ (∀ k : Fin (pathChainDepth s), S k.succ ⊆ S k.castSucc) ∧
      j₀ ∈ S (Fin.last _) ∧ ∀ i, (S i).card = (pathChainSizes s i).val := by
  unfold pathFams
  simp only [mem_filter, mem_univ, true_and]

section fam

variable {s : PathChain n m} {j₀ : Fin m} {S : Fin (pathChainDepth s + 1) → Finset (Fin m)}

theorem fam_cell_card (hS : S ∈ pathFams s j₀) (j : Fin (pathChainDepth s + 1)) :
    (cell S j).card = pathCellSize s j := by
  obtain ⟨-, hnest, -, hsz⟩ := mem_pathFams.mp hS
  unfold cell nextSet pathCellSize
  by_cases h : j.val < pathChainDepth s
  · have h' : j.val + 1 < pathChainDepth s + 1 := by omega
    rw [dif_pos h', dif_pos h,
      card_sdiff_of_subset (subset_of_nest hnest (k := j) (l := ⟨j.val + 1, h'⟩) (by simp)), hsz, hsz]
  · rw [dif_neg (show ¬ (j.val + 1 < pathChainDepth s + 1) by omega), dif_neg h, sdiff_empty, hsz]

theorem fam_quality (hS : S ∈ pathFams s j₀) (k : Fin (pathChainDepth s)) :
    fixedPathQuality S k = pathQuality s k := by
  obtain ⟨-, hnest, -, hsz⟩ := mem_pathFams.mp hS
  unfold fixedPathQuality pathQuality
  rw [card_sdiff_of_subset (hnest k), hsz, hsz, pathCellSize_castSucc]

/-- Splitting a product over the rows into the unscheduled rows and the rows `ρ(j)`. -/
theorem prod_rows_split {d : ℕ} (rho : Fin d ↪ Fin n) (f : Fin n → ℚ) :
    ∏ i, f i = (∏ i ∈ univ.filter (fun i => ∀ j, rho j ≠ i), f i) * ∏ j, f (rho j) := by
  rw [← prod_filter_mul_prod_filter_not univ (fun i => ∀ j, rho j ≠ i) f]
  congr 1
  have : univ.filter (fun i => ¬ ∀ j, rho j ≠ i) = univ.map rho := by
    ext i
    simp
  rw [this, prod_map]

/-- **The count for one family.** -/
theorem card_path_fixed (hn : 0 < n) (hS : S ∈ pathFams s j₀) :
    (((univ.filter (fun A : ValidTable n m =>
        ∀ i : Fin (pathChainDepth s + 1), candidateAt A.1 j₀ hn i = S i)).card : ℤ) : ℚ) =
      pathPartSum s := by
  obtain ⟨h0, hnest, hj₀, hsz⟩ := mem_pathFams.mp hS
  have h2 : ∀ k : Fin (pathChainDepth s), 2 ≤ (S k.castSucc).card := fun k => by
    rw [hsz]; exact chain_two_le s _
  rw [card_path_cells hn S j₀ h0 h2]
  have hrc : ∀ (rho : Fin (pathChainDepth s) ↪ Fin n)
      (ps : (j : Fin (pathChainDepth s + 1)) → OrderedFinpartition (cell S j).card),
      (∏ j, mu (ps j)) * ∏ i : Fin n,
        ((univ.filter (fun row : Row m => fixedPathRowAdmissible S j₀ rho i row ∧
          ∀ j, ConstOn (ps j) (fun t => row (cellEmb S j t)))).card : ℤ) =
      (∏ j, mu (ps j)) * ∏ i : Fin n,
        (cntU (m + 1) (fun j v => typeVec (ps j) v.val) (fun i => (S i).card)
          (fixedPathQuality S) rho i : ℤ) := by
    intro rho ps
    congr 1
    apply prod_congr rfl
    intro i _
    rw [rowcount_eq_cntU h0 hnest j₀ hj₀ (m + 1) (by omega) ps rho i]
  rw [sum_congr rfl (fun rho _ => sum_congr rfl (fun ps _ => hrc rho ps))]
  push_cast
  have hK : ∀ rho : Fin (pathChainDepth s) ↪ Fin n,
      ∑ ps : (j : Fin (pathChainDepth s + 1)) → OrderedFinpartition (cell S j).card,
        (∏ j, (mu (ps j) : ℚ)) * ∏ i : Fin n,
          (cntU (m + 1) (fun j v => typeVec (ps j) v.val) (fun i => (S i).card)
            (fixedPathQuality S) rho i : ℚ) =
      ∑ parts : PathPartitionTypes s, (∏ j, pathCoeff (parts j)) *
        (((∏ r ∈ univ.filter (fun r : Fin n => ∀ j, rho j ≠ r),
          pathW s parts (pathBefore s rho r)) *
          ∏ j, pathV s parts j (pathBefore s rho (rho j)) : ℕ) : ℚ) := by
    intro rho
    have hg := sum_mu_pi (m := m) (fun j => (cell S j).card) (pathCellSize s)
      (fun j => fam_cell_card hS j) (fun j => pathCellSize_le s j)
      (fun U => ∏ i : Fin n, (cntU (m + 1) U (fun i => (S i).card) (fixedPathQuality S) rho i : ℚ))
    push_cast at hg
    rw [hg]
    apply sum_congr rfl
    intro parts _
    congr 1
    push_cast
    rw [prod_rows_split rho]
    congr 1
    · apply prod_congr rfl
      intro r hr
      rw [cntU_W parts _ _ hsz (fam_quality hS) rho r (mem_filter.mp hr).2]
    · apply prod_congr rfl
      intro j _
      rw [cntU_V parts _ _ hsz (fam_quality hS) rho j]
  rw [sum_congr rfl (fun rho _ => hK rho), sum_comm]
  unfold pathPartSum pathF
  apply sum_congr rfl
  intro parts _
  rw [← mul_sum]
  push_cast
  rfl

end fam

end GradientKey.Concrete
