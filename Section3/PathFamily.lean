import PathFixed

/-!
# Proposition 3.2: the number of families of candidate sets

The number of families `S₀ = T₀ ⊇ S₁ ⊇ … ⊇ S_d` with `|S_i| = s_i` and `j₀ ∈ S_d` is
`∏_{k<d} C(s_k - 1, s_{k+1} - 1)`: `S_{k+1}` is `j₀` together with `s_{k+1} - 1` of the other
`s_k - 1` columns of `S_k` (`famCount_eq`). For a chain, `|pathFams s j₀| = ∏_{j<d} C(s_j-1, s_{j+1}-1)`
(`card_pathFams`).
-/

noncomputable section

namespace GradientKey.Concrete

open Finset Classical

variable {m : ℕ}

/-- The families of `d+1` nested sets starting at `T₀`, with sizes `sz`, containing `j₀`. -/
def famSet (j₀ : Fin m) (d : ℕ) (sz : Fin (d + 1) → ℕ) (T₀ : Finset (Fin m)) :
    Finset (Fin (d + 1) → Finset (Fin m)) :=
  univ.filter (fun S => S 0 = T₀ ∧ (∀ k : Fin d, S k.succ ⊆ S k.castSucc) ∧
    j₀ ∈ S (Fin.last d) ∧ ∀ i, (S i).card = sz i)

theorem mem_famSet {j₀ : Fin m} {d : ℕ} {sz : Fin (d + 1) → ℕ} {T₀ : Finset (Fin m)}
    {S : Fin (d + 1) → Finset (Fin m)} :
    S ∈ famSet j₀ d sz T₀ ↔ S 0 = T₀ ∧ (∀ k : Fin d, S k.succ ⊆ S k.castSucc) ∧
      j₀ ∈ S (Fin.last d) ∧ ∀ i, (S i).card = sz i := by
  unfold famSet
  simp only [mem_filter, mem_univ, true_and]

/-- The subsets of `T₀` of size `k` containing `j₀`. -/
def subSet (j₀ : Fin m) (T₀ : Finset (Fin m)) (k : ℕ) : Finset (Finset (Fin m)) :=
  T₀.powerset.filter (fun T => j₀ ∈ T ∧ T.card = k)

theorem card_subSet (j₀ : Fin m) (T₀ : Finset (Fin m)) (k : ℕ) (hj : j₀ ∈ T₀) (hk : 1 ≤ k) :
    (subSet j₀ T₀ k).card = (T₀.card - 1).choose (k - 1) := by
  rw [← card_erase_of_mem hj, ← card_powersetCard]
  refine card_bij' (fun T _ => T.erase j₀) (fun T _ => insert j₀ T) ?_ ?_ ?_ ?_
  · intro T hT
    simp only [subSet, mem_filter, mem_powerset] at hT
    rw [mem_powersetCard]
    refine ⟨erase_subset_erase _ hT.1, ?_⟩
    rw [card_erase_of_mem hT.2.1, hT.2.2]
  · intro T hT
    rw [mem_powersetCard] at hT
    simp only [subSet, mem_filter, mem_powerset]
    have hj' : j₀ ∉ T := fun h => by
      have := hT.1 h
      simp at this
    refine ⟨insert_subset hj (hT.1.trans (erase_subset _ _)), mem_insert_self _ _, ?_⟩
    rw [card_insert_of_notMem hj', hT.2]
    omega
  · intro T hT
    simp only [subSet, mem_filter] at hT
    exact insert_erase hT.2.1
  · intro T hT
    rw [mem_powersetCard] at hT
    apply erase_insert
    intro h
    have := hT.1 h
    simp at this

/-- Removing the first set of a family. -/
theorem famSet_succ (j₀ : Fin m) (d : ℕ) (sz : Fin (d + 2) → ℕ) (T₀ : Finset (Fin m))
    (hT₀ : T₀.card = sz 0) :
    (famSet j₀ (d + 1) sz T₀).card =
      ∑ T₁ ∈ subSet j₀ T₀ (sz 1), (famSet j₀ d (Fin.tail sz) T₁).card := by
  rw [card_eq_sum_card_fiberwise (f := fun S => S 1) (t := subSet j₀ T₀ (sz 1))]
  · apply sum_congr rfl
    intro T₁ hT₁
    simp only [subSet, mem_filter, mem_powerset] at hT₁
    refine card_bij' (fun S _ => Fin.tail S) (fun S' _ => Fin.cons T₀ S') ?_ ?_ ?_ ?_
    · intro S hS
      rw [mem_filter, mem_famSet] at hS
      obtain ⟨⟨h0, hnest, hj, hsz⟩, h1⟩ := hS
      rw [mem_famSet]
      refine ⟨h1, ?_, ?_, ?_⟩
      · intro k
        have := hnest k.succ
        simp only [Fin.tail, ← Fin.succ_castSucc] at this ⊢
        exact this
      · simp only [Fin.tail, Fin.succ_last]; exact hj
      · intro i; simp only [Fin.tail]; exact hsz _
    · intro S' hS'
      rw [mem_famSet] at hS'
      obtain ⟨h0, hnest, hj, hsz⟩ := hS'
      rw [mem_filter, mem_famSet]
      refine ⟨⟨Fin.cons_zero _ _, ?_, ?_, ?_⟩, ?_⟩
      · intro k
        refine Fin.cases ?_ (fun k' => ?_) k
        · simp only [Fin.succ_zero_eq_one, Fin.castSucc_zero]
          rw [← Fin.succ_zero_eq_one, Fin.cons_succ, Fin.cons_zero, h0]
          exact hT₁.1
        · rw [← Fin.succ_castSucc, Fin.cons_succ, Fin.cons_succ]
          exact hnest k'
      · rw [← Fin.succ_last, Fin.cons_succ]; exact hj
      · intro i
        refine Fin.cases ?_ (fun i' => ?_) i
        · rw [Fin.cons_zero]; exact hT₀
        · rw [Fin.cons_succ]; exact hsz i'
      · show (Fin.cons T₀ S' : Fin (d + 2) → Finset (Fin m)) 1 = T₁
        rw [← Fin.succ_zero_eq_one, Fin.cons_succ, h0]
    · intro S hS
      rw [mem_filter, mem_famSet] at hS
      rw [← hS.1.1]
      exact Fin.cons_self_tail S
    · intro S' _
      exact Fin.tail_cons _ _
  · intro S hS
    rw [mem_coe, mem_famSet] at hS
    obtain ⟨h0, hnest, hj, hsz⟩ := hS
    simp only [subSet, mem_coe, mem_filter, mem_powerset]
    have hsub : ∀ k : Fin (d + 2), S k ⊆ S 0 := fun k =>
      subset_of_nest hnest (k := 0) (l := k) (Nat.zero_le _)
    refine ⟨h0 ▸ hsub 1, ?_, hsz 1⟩
    exact subset_of_nest hnest (k := 1) (l := Fin.last _) (by simp) hj

/-- **Number of families of candidate sets.** -/
theorem famCount_eq (j₀ : Fin m) : ∀ (d : ℕ) (sz : Fin (d + 1) → ℕ) (T₀ : Finset (Fin m)),
    (∀ i, 1 ≤ sz i) → j₀ ∈ T₀ → T₀.card = sz 0 →
    (famSet j₀ d sz T₀).card = ∏ k : Fin d, (sz k.castSucc - 1).choose (sz k.succ - 1)
  | 0, sz, T₀, _, hj, hT => by
    rw [Fintype.prod_empty, card_eq_one]
    refine ⟨fun _ => T₀, ?_⟩
    ext S
    rw [mem_famSet, mem_singleton]
    constructor
    · rintro ⟨h0, -⟩
      funext i
      rw [Fin.fin_one_eq_zero i, h0]
    · rintro rfl
      refine ⟨rfl, fun k => k.elim0, hj, fun i => ?_⟩
      rw [Fin.fin_one_eq_zero i]
      exact hT
  | d + 1, sz, T₀, hsz, hj, hT => by
    rw [famSet_succ j₀ d sz T₀ hT]
    have hin : ∀ T₁ ∈ subSet j₀ T₀ (sz 1),
        (famSet j₀ d (Fin.tail sz) T₁).card =
          ∏ k : Fin d, (Fin.tail sz k.castSucc - 1).choose (Fin.tail sz k.succ - 1) := by
      intro T₁ hT₁
      simp only [subSet, mem_filter] at hT₁
      exact famCount_eq j₀ d (Fin.tail sz) T₁ (fun i => hsz _) hT₁.2.1 hT₁.2.2
    rw [sum_congr rfl hin, sum_const, card_subSet j₀ T₀ _ hj (hsz 1), smul_eq_mul, hT,
      Fin.prod_univ_succ]
    congr 1

/-- **The families of candidate sets of a chain.** -/
theorem card_pathFams {n : ℕ} (s : PathChain n m) (j₀ : Fin m) :
    (pathFams s j₀).card = pathFamilyFactor s := by
  have h := famCount_eq j₀ (pathChainDepth s) (fun i => (pathChainSizes s i).val) univ
    (fun i => by have := chain_two_le s i; omega) (mem_univ _)
    (by rw [card_univ, Fintype.card_fin, chain_zero])
  unfold pathFams pathFamilyFactor
  unfold famSet at h
  exact h

end GradientKey.Concrete
