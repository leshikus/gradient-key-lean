import PathPrune
import Examples

/-!
# Proposition 3.1: the example `(n,m) = (3,4)`

Checks of the definitions of `PathDefs` on the article's example. `W`, `V_j` and `F_n` are evaluated through
copies with computable instances (`wDec`, `vDec`, `fDec`), proved equal to the definitions.

* `c((1,1)) = 1`, `c((2)) = -1`; the integer partitions of `2` are `(1,1)` and `(2)` (`sum_pp2`).
* Chain `(4,2)`: `(W(∅), W({0})) = (10,16)` for `((1,1),(1,1))`, `(6,8)` with `(2)` in one cell, `(2,4)` for
  `((2),(2))`; `V_0 = 2`; `F_3 = 1032, 296, 56`.
* The chain terms of Proposition 3.1 sum to `3408 = (2^3)_4 · t_{3,4}(G)` (`path_formula_n3_m4_total`).
-/

open Finset

namespace GradientKey.Concrete

instance decIsPathChain (m d : ℕ) (s : PathSizeVector m d) : Decidable (IsPathChain m d s) := by
  unfold IsPathChain; infer_instance

instance decMeets {n m : ℕ} (s : PathChain n m) (parts : PathPartitionTypes s) (bits : PathAssignment s parts)
    (M : Finset (Fin (pathChainDepth s))) (j : Fin (pathChainDepth s)) :
    Decidable (pathMeetsQuality s parts bits M j) :=
  decidable_of_iff ((j ∈ M ∧ pathRowQuality s parts bits j.castSucc ≤ pathQuality s j) ∨
      (j ∉ M ∧ pathRowQuality s parts bits j.castSucc < pathQuality s j)) (by
    unfold pathMeetsQuality
    by_cases h : j ∈ M <;> simp [h])

/-- `W(M)` with computable instances. -/
def wDec {n m : ℕ} (s : PathChain n m) (parts : PathPartitionTypes s)
    (M : Finset (Fin (pathChainDepth s))) : ℕ :=
  (univ.filter (fun bits : PathAssignment s parts =>
    ∀ j : Fin (pathChainDepth s), pathMeetsQuality s parts bits M j)).card

/-- `V_j(M)` with computable instances. -/
def vDec {n m : ℕ} (s : PathChain n m) (parts : PathPartitionTypes s) (j : Fin (pathChainDepth s))
    (M : Finset (Fin (pathChainDepth s))) : ℕ :=
  (univ.filter (fun bits : PathAssignment s parts =>
    (∃ b : Bool, (∀ block : PathBlocks s parts,
        (block.1.val = j.val → bits block = !b) ∧ (j.val < block.1.val → bits block = b))) ∧
    (∀ i : Fin (pathChainDepth s), i.val < j.val → pathMeetsQuality s parts bits M i))).card

/-- `F_n` with computable instances, summed over injective maps. -/
def fDec {n m : ℕ} (s : PathChain n m) (parts : PathPartitionTypes s) : ℕ :=
  ∑ rho : {f : Fin (pathChainDepth s) → Fin n // Function.Injective f},
    (∏ r ∈ univ.filter (fun r : Fin n => ∀ j : Fin (pathChainDepth s), rho.1 j ≠ r),
      wDec s parts (univ.filter (fun j => rho.1 j < r))) *
    ∏ j : Fin (pathChainDepth s), vDec s parts j (univ.filter (fun j' => rho.1 j' < rho.1 j))

theorem pathW_eq_wDec {n m : ℕ} (s : PathChain n m) (parts : PathPartitionTypes s)
    (M : Finset (Fin (pathChainDepth s))) : pathW s parts M = wDec s parts M :=
  card_filter_inst _

theorem pathV_eq_vDec {n m : ℕ} (s : PathChain n m) (parts : PathPartitionTypes s)
    (j : Fin (pathChainDepth s)) (M : Finset (Fin (pathChainDepth s))) :
    pathV s parts j M = vDec s parts j M :=
  card_filter_inst _

theorem pathF_eq_fDec {n m : ℕ} (s : PathChain n m) (parts : PathPartitionTypes s) :
    pathF s parts = fDec s parts := by
  unfold pathF fDec
  rw [← (Equiv.subtypeInjectiveEquivEmbedding _ _).sum_comp]
  apply sum_congr rfl
  intro f _
  simp only [pathBefore, pathW_eq_wDec, pathV_eq_vDec]
  rfl

/-! Integer partitions of `2` as multiplicity vectors. -/

def U11 : Fin 5 → Fin 5 := ![0, 2, 0, 0, 0]
def U2 : Fin 5 → Fin 5 := ![0, 0, 1, 0, 0]

theorem vec5_ext (u w : Fin 5 → Fin 5) (h1 : (u 0).val = (w 0).val) (h2 : (u 1).val = (w 1).val)
    (h3 : (u 2).val = (w 2).val) (h4 : (u 3).val = (w 3).val) (h5 : (u 4).val = (w 4).val) : u = w := by
  funext v
  fin_cases v
  · exact Fin.ext h1
  · exact Fin.ext h2
  · exact Fin.ext h3
  · exact Fin.ext h4
  · exact Fin.ext h5

theorem pp_sum5 {a : ℕ} (p : PathPartition 4 a) :
    (p.1 0).val = 0 ∧ (p.1 1).val + 2 * (p.1 2).val + 3 * (p.1 3).val + 4 * (p.1 4).val = a := by
  refine ⟨p.2.1, ?_⟩
  have h := p.2.2
  rw [Fin.sum_univ_five] at h
  simp at h
  omega

theorem sum_pp2 (a : ℕ) (h : a = 2) (f : PathPartition 4 a → ℚ) :
    ∑ p, f p = f ⟨U11, by subst h; decide⟩ + f ⟨U2, by subst h; decide⟩ := by
  subst h
  have hu : (univ : Finset (PathPartition 4 2)) = {⟨U11, by decide⟩, ⟨U2, by decide⟩} := by
    ext p
    simp only [mem_univ, mem_insert, mem_singleton, true_iff]
    obtain ⟨h0, hs⟩ := pp_sum5 p
    have a4 : (p.1 4).val = 0 := by omega
    have a3 : (p.1 3).val = 0 := by omega
    have key : ((p.1 1).val = 2 ∧ (p.1 2).val = 0) ∨ ((p.1 1).val = 0 ∧ (p.1 2).val = 1) := by
      have : (p.1 2).val ≤ 1 := by omega
      interval_cases h2 : (p.1 2).val <;> omega
    rcases key with ⟨a1, a2⟩ | ⟨a1, a2⟩
    · left; apply Subtype.ext; apply vec5_ext <;> simp [U11, a1, a2, a3, a4, h0]
    · right; apply Subtype.ext; apply vec5_ext <;> simp [U2, a1, a2, a3, a4, h0]
  rw [hu, sum_insert (by decide), sum_singleton]

theorem coeff_U11 (a : ℕ) (h) : pathCoeff (⟨U11, h⟩ : PathPartition 4 a) = 1 := by
  have ha : a = 2 := by have := h.2; rw [Fin.sum_univ_five] at this; simpa [U11] using this.symm
  subst ha
  unfold pathCoeff pathPartCount
  simp [Fin.sum_univ_five, Fin.prod_univ_five, U11]

theorem coeff_U2 (a : ℕ) (h) : pathCoeff (⟨U2, h⟩ : PathPartition 4 a) = -1 := by
  have ha : a = 2 := by have := h.2; rw [Fin.sum_univ_five] at this; simpa [U2] using this.symm
  subst ha
  unfold pathCoeff pathPartCount
  simp [Fin.sum_univ_five, Fin.prod_univ_five, U2]

end GradientKey.Concrete

namespace GradientKey.Concrete.Example34

open GradientKey.Concrete

/-- The chain `(4,2)` for `(n,m) = (3,4)`. -/
def chain42 : PathChain 3 4 := ⟨⟨1, ![4, 2]⟩, by decide⟩

theorem chain42_family : pathFamilyFactor chain42 = 3 := by decide

/-- Partitions of the two cells, given by multiplicity vectors. -/
def parts42 (a b : Fin 5 → Fin 5) (h : ((a 0).val = 0 ∧ ∑ v : Fin 5, v.val * (a v).val = 2) ∧
    ((b 0).val = 0 ∧ ∑ v : Fin 5, v.val * (b v).val = 2)) : PathPartitionTypes chain42 :=
  fun j => ⟨if j.val = 0 then a else b, by
    fin_cases j
    · exact h.1
    · exact h.2⟩

/-- `((1,1),(1,1))`. -/
def P11_11 : PathPartitionTypes chain42 := parts42 U11 U11 (by decide)
/-- `((2),(1,1))`. -/
def P2_11 : PathPartitionTypes chain42 := parts42 U2 U11 (by decide)
/-- `((1,1),(2))`. -/
def P11_2 : PathPartitionTypes chain42 := parts42 U11 U2 (by decide)
/-- `((2),(2))`. -/
def P2_2 : PathPartitionTypes chain42 := parts42 U2 U2 (by decide)

def d0 : Fin (pathChainDepth chain42) := ⟨0, by decide⟩

theorem example34_coeff (h1 h2) :
    pathCoeff (⟨U11, h1⟩ : PathPartition 4 2) = 1 ∧ pathCoeff (⟨U2, h2⟩ : PathPartition 4 2) = -1 :=
  ⟨coeff_U11 2 h1, coeff_U2 2 h2⟩

theorem example34_W :
    (pathW chain42 P11_11 ∅ = 10 ∧ pathW chain42 P11_11 {d0} = 16) ∧
    (pathW chain42 P2_11 ∅ = 6 ∧ pathW chain42 P2_11 {d0} = 8) ∧
    (pathW chain42 P11_2 ∅ = 6 ∧ pathW chain42 P11_2 {d0} = 8) ∧
    (pathW chain42 P2_2 ∅ = 2 ∧ pathW chain42 P2_2 {d0} = 4) := by
  simp only [pathW_eq_wDec]
  decide

theorem example34_V :
    pathV chain42 P11_11 d0 ∅ = 2 ∧ pathV chain42 P2_11 d0 ∅ = 2 ∧
    pathV chain42 P11_2 d0 ∅ = 2 ∧ pathV chain42 P2_2 d0 ∅ = 2 := by
  simp only [pathV_eq_vDec]
  decide

theorem example34_F :
    pathF chain42 P11_11 = 1032 ∧ pathF chain42 P2_11 = 296 ∧ pathF chain42 P11_2 = 296 ∧
    pathF chain42 P2_2 = 56 := by
  simp only [pathF_eq_fDec]
  decide

/-- The chain terms of Proposition 3.1 for `(n,m) = (3,4)` sum to `3408`. -/
theorem path_formula_n3_m4_total : ∑ s : PathChain 3 4, (pathChainTerm s : ℝ) = 3408 := by
  have h := prop_path_formula (n := 3) (m := 4) (by norm_num) (by norm_num)
  rw [example_n3_m4] at h
  unfold pathFormulaRHS at h
  rw [show Nat.descFactorial (2 ^ 3) 4 = 1680 from rfl] at h
  push_cast at h
  field_simp at h
  convert h.symm using 2
  congr 1; exact Subsingleton.elim _ _

end GradientKey.Concrete.Example34
