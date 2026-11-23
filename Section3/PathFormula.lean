import PathFamily
import PathFork
import PathChainBridge

/-!
# Proposition 3.2: the path formula

**Per-chain identity** (`chain_count`). For a chain `s` and a column `j₀`, the summand of `s` in
Proposition 3.2 equals the number of valid tables in which the path of `j₀` has candidate sets of sizes
`s₀,…,s_d`, i.e. a fork at depth `d` with these sizes.

**Formula** (`prop_path_formula`). Summing over chains and columns gives
`t_{n,m}(G) = (2^n)_m⁻¹ ∑_s (∏_{j<d} C(s_j-1, s_{j+1}-1)) ∑_{λ_0,…,λ_d} (∏_j c(λ_j)) F_n`, with the
existing `tG`.
-/

noncomputable section

namespace GradientKey.Concrete

open Finset Classical

variable {n m : ℕ}

/-- The column `j₀` has candidate sets of the sizes of the chain `s`. -/
def MatchesChain (A : ValidTable n m) (hn : 0 < n) (j₀ : Fin m) (s : PathChain n m) : Prop :=
  ∀ i : Fin (pathChainDepth s + 1), (candidateAt A.1 j₀ hn i).card = (pathChainSizes s i).val

theorem candidates_mem_pathFams (A : ValidTable n m) (hn : 0 < n) (j₀ : Fin m) (s : PathChain n m)
    (h : MatchesChain A hn j₀ s) :
    (fun i : Fin (pathChainDepth s + 1) => candidateAt A.1 j₀ hn i) ∈ pathFams s j₀ := by
  rw [mem_pathFams]
  refine ⟨rfl, fun k => ?_, p1_candidate_mem A.1 j₀ hn _, h⟩
  exact p1_candidate_subset_of_le A.1 j₀ hn (by simp)

/-- **Per-chain identity.** -/
theorem chain_count (hn : 0 < n) (s : PathChain n m) (j₀ : Fin m) :
    (((univ.filter (fun A : ValidTable n m => MatchesChain A hn j₀ s)).card : ℕ) : ℚ) =
      pathChainTerm s := by
  rw [card_eq_sum_card_fiberwise (f := fun A i => candidateAt A.1 j₀ hn (i : Fin (pathChainDepth s + 1)))
    (t := pathFams s j₀) (fun A hA => candidates_mem_pathFams A hn j₀ s (mem_filter.mp hA).2)]
  have hfib : ∀ S ∈ pathFams s j₀,
      ((univ.filter (fun A : ValidTable n m => MatchesChain A hn j₀ s)).filter
        (fun A => (fun i : Fin (pathChainDepth s + 1) => candidateAt A.1 j₀ hn i) = S)) =
      univ.filter (fun A : ValidTable n m =>
        ∀ i : Fin (pathChainDepth s + 1), candidateAt A.1 j₀ hn i = S i) := by
    intro S hS
    obtain ⟨-, -, -, hsz⟩ := mem_pathFams.mp hS
    rw [filter_filter]
    apply filter_congr
    intro A _
    rw [funext_iff]
    constructor
    · exact fun h => h.2
    · intro h
      refine ⟨fun i => ?_, h⟩
      rw [h i, hsz]
  push_cast
  rw [sum_congr rfl (fun S hS => by rw [hfib S hS])]
  have hfix : ∀ S ∈ pathFams s j₀,
      ((univ.filter (fun A : ValidTable n m =>
        ∀ i : Fin (pathChainDepth s + 1), candidateAt A.1 j₀ hn i = S i)).card : ℚ) = pathPartSum s := by
    intro S hS
    have := card_path_fixed hn hS
    push_cast at this
    exact this
  rw [sum_congr rfl hfix, sum_const, card_pathFams, nsmul_eq_mul]
  rfl

/-- Each table with a fork at depth `i < n` matches exactly one chain, of depth `i`. -/
theorem card_matching_chains (A : ValidTable n m) (hn : 0 < n) (j : Fin m) :
    (univ.filter (fun s : PathChain n m => MatchesChain A hn j s)).card =
      ((range n).filter (fun i => 2 ≤ (candidateAt A.1 j hn i).card)).card := by
  refine card_bij (fun s _ => pathChainDepth s) ?_ ?_ ?_
  · intro s hs
    rw [mem_filter] at hs ⊢
    refine ⟨mem_range.mpr s.1.1.isLt, ?_⟩
    have := hs.2 (Fin.last _)
    simp only [Fin.val_last] at this
    rw [this]
    exact chain_last_ge s
  · rintro ⟨⟨d, v⟩, hv⟩ hs ⟨⟨d', v'⟩, hv'⟩ hs' hdd
    rw [mem_filter] at hs hs'
    have hd : d = d' := Fin.ext hdd
    subst hd
    have : v = v' := by
      funext i
      apply Fin.ext
      have h1 := hs.2 i
      have h2 := hs'.2 i
      unfold pathChainSizes at h1 h2
      simp only at h1 h2
      rw [← h1, ← h2]
    subst this
    rfl
  · intro i hi
    rw [mem_filter] at hi
    refine ⟨pathChainOfFork A hn j i hi.2, ?_, pathChainOfFork_depth A hn j i hi.2⟩
    rw [mem_filter]
    exact ⟨mem_univ _, fun k => (pathChainOfFork_sizes A hn j i hi.2 k).symm⟩

/-- The fork counts of a column, summed over depths, are the chain counts summed over chains. -/
theorem sum_forkTableCount_eq (hn : 0 < n) (j : Fin m) :
    ∑ i ∈ range n, forkTableCount n m hn j i =
      ∑ s : PathChain n m, (univ.filter (fun A : ValidTable n m => MatchesChain A hn j s)).card := by
  unfold forkTableCount
  simp only [card_filter]
  rw [sum_comm, sum_comm (s := (univ : Finset (PathChain n m)))]
  apply sum_congr rfl
  intro A _
  rw [← card_filter, ← card_filter, card_matching_chains]

/-- **Proposition 3.2.** -/
theorem prop_path_formula (hn : 0 < n) (hm : 2 ≤ m) : tG n m hn = pathFormulaRHS n m := by
  rw [tG_eq_forkTableCounts hn hm]
  unfold pathFormulaRHS
  have hcol : ∀ j : Fin m, ∑ i ∈ range n, (forkTableCount n m hn j i : ℝ) =
      ∑ s : PathChain n m, ((pathChainTerm s : ℚ) : ℝ) := by
    intro j
    have h := sum_forkTableCount_eq hn j
    have h' : ((∑ i ∈ range n, forkTableCount n m hn j i : ℕ) : ℝ) =
        ((∑ s : PathChain n m,
          (univ.filter (fun A : ValidTable n m => MatchesChain A hn j s)).card : ℕ) : ℝ) := by
      rw [h]
    push_cast at h'
    rw [h']
    apply sum_congr rfl
    intro s _
    rw [← chain_count hn s j]
    push_cast
    rfl
  rw [sum_congr rfl (fun j _ => hcol j), sum_const, card_univ, Fintype.card_fin, nsmul_eq_mul]
  have hm0 : (m : ℝ) ≠ 0 := by positivity
  rw [mul_div_mul_left _ _ hm0]

/-- **Proposition 3.2**, as stated in the article: for each chain `s` fix any nested candidate sets `S s` of its
sizes, with column `j₀ = 0` in the last one. Then `(2^n)_m t_{n,m}(G)` is the sum over chains of the number of
families times `∑_ρ ∑_p μ(p) ∏_i r_i^ρ(p)`, where `r_i^ρ(p)` counts the rows satisfying the path conditions on row
`i` (`fixedPathRowAdmissible`) that are constant on the blocks of `p`. -/
theorem prop_path_formula_sets (hn : 0 < n) (hm : 2 ≤ m)
    (S : (s : PathChain n m) → Fin (pathChainDepth s + 1) → Finset (Fin m))
    (hS : ∀ s, S s ∈ pathFams s ⟨0, by omega⟩) :
    tG n m hn = (∑ s : PathChain n m, (((pathFamilyFactor s : ℤ) *
        ∑ rho : Fin (pathChainDepth s) ↪ Fin n, ∑ c : OrderedFinpartition m,
          mu c * ∏ i : Fin n, ((univ.filter (fun row : Row m =>
            fixedPathRowAdmissible (S s) ⟨0, by omega⟩ rho i row ∧ ConstOn c row)).card : ℤ) : ℤ) : ℝ))
      / (((2 ^ n).descFactorial m : ℕ) : ℝ) := by
  have hpt : ∀ s : PathChain n m, ((pathChainTerm s : ℚ) : ℝ) = (((pathFamilyFactor s : ℤ) *
      ∑ rho : Fin (pathChainDepth s) ↪ Fin n, ∑ c : OrderedFinpartition m,
        mu c * ∏ i : Fin n, ((univ.filter (fun row : Row m =>
          fixedPathRowAdmissible (S s) ⟨0, by omega⟩ rho i row ∧ ConstOn c row)).card : ℤ) : ℤ) : ℝ) := by
    intro s
    obtain ⟨h0, _, _, hsz⟩ := mem_pathFams.mp (hS s)
    have h2 : ∀ j : Fin (pathChainDepth s), 2 ≤ (S s j.castSucc).card := fun j => by
      rw [hsz]; exact chain_two_le s _
    have e1 := card_path_eq hn (S s) ⟨0, by omega⟩ h0 h2
    have e2 := card_path_fixed hn (hS s)
    rw [← e1]
    have : pathChainTerm s = (pathFamilyFactor s : ℚ) * pathPartSum s := rfl
    rw [this, ← e2]
    push_cast
    rfl
  rw [prop_path_formula hn hm]
  unfold pathFormulaRHS
  simp only [hpt]

/-- Every chain term is a natural number: by `chain_count` it counts tables, although its Möbius expansion has
negative summands. -/
theorem chain_term_natural (s : PathChain n m) : ∃ k : ℕ, (k : ℚ) = pathChainTerm s := by
  have hn : 0 < n := Fin.pos s.1.1
  have hm : 0 < m := by have h0 := chain_zero s; have h2 := chain_two_le s 0; omega
  exact ⟨_, chain_count hn s ⟨0, hm⟩⟩

theorem chain_term_nonneg (s : PathChain n m) : 0 ≤ pathChainTerm s := by
  obtain ⟨k, hk⟩ := chain_term_natural s
  rw [← hk]; positivity

/-- A chain of depth `0` is matched by every valid table, so its term is `(2^n)_m`. -/
theorem path_chain_term_depth_zero (s : PathChain n m) (hd : pathChainDepth s = 0) :
    pathChainTerm s = ((2 ^ n).descFactorial m : ℚ) := by
  have hn : 0 < n := Fin.pos s.1.1
  have hm : 0 < m := by have h0 := chain_zero s; have h2 := chain_two_le s 0; omega
  have hmatch : ∀ A : ValidTable n m, MatchesChain A hn ⟨0, hm⟩ s := by
    intro A i
    have hi : i = 0 := Fin.ext (by have := i.isLt; omega)
    subst hi
    rw [chain_zero s]
    show (candidateAt A.1 ⟨0, hm⟩ hn 0).card = m
    simp [candidateAt]
  rw [← chain_count hn s ⟨0, hm⟩, ← card_valid, ← Finset.card_univ]
  congr 2
  ext A; simp [hmatch A]

end GradientKey.Concrete
