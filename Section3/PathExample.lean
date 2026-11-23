import PathPrune
import Examples

/-!
# Proposition 3.2: the example `(n,m) = (3,4)`

Checks of the definitions of `PathDefs` on the article's example. `W`, `V_j` and `F_n` are evaluated through
copies with computable instances (`wDec`, `vDec`, `fDec`), proved equal to the definitions.

* `c((1,1)) = 1`, `c((2)) = -1`; the integer partitions of `2` are `(1,1)` and `(2)` (`sum_pp2`).
* Chain `(4,2)`: `(W(∅), W({0})) = (10,16)` for `((1,1),(1,1))`, `(6,8)` with `(2)` in one cell, `(2,4)` for
  `((2),(2))`; `V_0 = 2`; `F_3 = 1032, 296, 56`.
* Chains `(4,3)`: `c = 1, -3, 2`, `F_3 = 248, 104, 56`; `(4,3,2)`: `F_3 = 64, 48`.
* The chains are `(4)`, `(4,2)`, `(4,3)`, `(4,3,2)` (`example34_chains`), with terms `1680`, `1488`, `144`, `96`.
  Hence `pathFormulaRHS 3 4 = 3408/1680` (`example34_rhs`) and, by Proposition 3.2, `t_{3,4}(G) = 3408/1680`
  (`example34_tG`), the value of `example_n3_m4`.
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

theorem pp2_cases {a : ℕ} (h : a = 2) (p : PathPartition 4 a) : p.1 = U11 ∨ p.1 = U2 := by
  subst h
  obtain ⟨h0, hs⟩ := pp_sum5 p
  have a4 : (p.1 4).val = 0 := by omega
  have a3 : (p.1 3).val = 0 := by omega
  have key : ((p.1 1).val = 2 ∧ (p.1 2).val = 0) ∨ ((p.1 1).val = 0 ∧ (p.1 2).val = 1) := by
    have : (p.1 2).val ≤ 1 := by omega
    interval_cases h2 : (p.1 2).val <;> omega
  rcases key with ⟨a1, a2⟩ | ⟨a1, a2⟩
  · left; apply vec5_ext <;> simp [U11, a1, a2, a3, a4, h0]
  · right; apply vec5_ext <;> simp [U2, a1, a2, a3, a4, h0]

theorem coeff_of_U11 {a : ℕ} (p : PathPartition 4 a) (h : p.1 = U11) : pathCoeff p = 1 := by
  obtain ⟨u, hu⟩ := p; subst h; exact coeff_U11 _ _

theorem coeff_of_U2 {a : ℕ} (p : PathPartition 4 a) (h : p.1 = U2) : pathCoeff p = -1 := by
  obtain ⟨u, hu⟩ := p; subst h; exact coeff_U2 _ _

/-! Integer partitions of `1` and `3`. -/

def U1 : Fin 5 → Fin 5 := ![0, 1, 0, 0, 0]
def U111 : Fin 5 → Fin 5 := ![0, 3, 0, 0, 0]
def U21 : Fin 5 → Fin 5 := ![0, 1, 1, 0, 0]
def U3 : Fin 5 → Fin 5 := ![0, 0, 0, 1, 0]

theorem pp1_cases {a : ℕ} (h : a = 1) (p : PathPartition 4 a) : p.1 = U1 := by
  subst h
  obtain ⟨h0, hs⟩ := pp_sum5 p
  have a4 : (p.1 4).val = 0 := by omega
  have a3 : (p.1 3).val = 0 := by omega
  have a2 : (p.1 2).val = 0 := by omega
  have a1 : (p.1 1).val = 1 := by omega
  apply vec5_ext <;> simp [U1, a1, a2, a3, a4, h0]

theorem pp3_cases {a : ℕ} (h : a = 3) (p : PathPartition 4 a) :
    p.1 = U111 ∨ p.1 = U21 ∨ p.1 = U3 := by
  subst h
  obtain ⟨h0, hs⟩ := pp_sum5 p
  have a4 : (p.1 4).val = 0 := by omega
  have b3 : (p.1 3).val ≤ 1 := by omega
  interval_cases a3 : (p.1 3).val
  · have b2 : (p.1 2).val ≤ 1 := by omega
    interval_cases a2 : (p.1 2).val
    · have a1 : (p.1 1).val = 3 := by omega
      left; apply vec5_ext <;> simp [U111, a1, a2, a3, a4, h0]
    · have a1 : (p.1 1).val = 1 := by omega
      right; left; apply vec5_ext <;> simp [U21, a1, a2, a3, a4, h0]
  · have a2 : (p.1 2).val = 0 := by omega
    have a1 : (p.1 1).val = 0 := by omega
    right; right; apply vec5_ext <;> simp [U3, a1, a2, a3, a4, h0]

theorem coeff_of_U1 {a : ℕ} (p : PathPartition 4 a) (h : p.1 = U1) : pathCoeff p = 1 := by
  obtain ⟨u, hu⟩ := p; subst h
  have ha : a = 1 := by have := hu.2; rw [Fin.sum_univ_five] at this; simpa [U1] using this.symm
  subst ha
  unfold pathCoeff pathPartCount
  simp [Fin.sum_univ_five, Fin.prod_univ_five, U1]

theorem coeff_of_U111 {a : ℕ} (p : PathPartition 4 a) (h : p.1 = U111) : pathCoeff p = 1 := by
  obtain ⟨u, hu⟩ := p; subst h
  have ha : a = 3 := by have := hu.2; rw [Fin.sum_univ_five] at this; simpa [U111] using this.symm
  subst ha
  unfold pathCoeff pathPartCount
  simp [Fin.sum_univ_five, Fin.prod_univ_five, U111]
  norm_num [Nat.factorial]

theorem coeff_of_U21 {a : ℕ} (p : PathPartition 4 a) (h : p.1 = U21) : pathCoeff p = -3 := by
  obtain ⟨u, hu⟩ := p; subst h
  have ha : a = 3 := by have := hu.2; rw [Fin.sum_univ_five] at this; simpa [U21] using this.symm
  subst ha
  unfold pathCoeff pathPartCount
  simp [Fin.sum_univ_five, Fin.prod_univ_five, U21]
  norm_num [Nat.factorial]

theorem coeff_of_U3 {a : ℕ} (p : PathPartition 4 a) (h : p.1 = U3) : pathCoeff p = 2 := by
  obtain ⟨u, hu⟩ := p; subst h
  have ha : a = 3 := by have := hu.2; rw [Fin.sum_univ_five] at this; simpa [U3] using this.symm
  subst ha
  unfold pathCoeff pathPartCount
  simp [Fin.sum_univ_five, Fin.prod_univ_five, U3]
  norm_num [Nat.factorial]

/-- Two chains of the same depth are equal if their sizes agree. -/
theorem chain_eq_of {n m : ℕ} {d : Fin n} (v w : PathSizeVector m d.val) (hv : IsPathChain m d.val v)
    (hw : IsPathChain m d.val w) (h : ∀ i, (v i).val = (w i).val) :
    (⟨⟨d, v⟩, hv⟩ : PathChain n m) = ⟨⟨d, w⟩, hw⟩ := by
  have : v = w := funext fun i => Fin.ext (h i)
  subst this; rfl

end GradientKey.Concrete

namespace GradientKey.Concrete.Example34

open GradientKey.Concrete

/-- The depth-zero chain `(4)`. -/
def chain4 : PathChain 3 4 := ⟨⟨0, ![4]⟩, by decide⟩

theorem example34_chain4 : pathChainTerm chain4 = 1680 := by
  rw [path_chain_term_depth_zero chain4 rfl]; rfl

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

def i0 : Fin (pathChainDepth chain42 + 1) := 0
def i1 : Fin (pathChainDepth chain42 + 1) := 1

theorem chain42_univ :
    (univ : Finset (PathPartitionTypes chain42)) = {P11_11, P2_11, P11_2, P2_2} := by
  ext x
  simp only [mem_univ, mem_insert, mem_singleton, true_iff]
  have e0 := pp2_cases (by decide) (x i0)
  have e1 := pp2_cases (by decide) (x i1)
  have key : ∀ P : PathPartitionTypes chain42, (P i0).1 = (x i0).1 →
      (P i1).1 = (x i1).1 → x = P := by
    intro P h0 h1
    funext ⟨j, hj⟩
    apply Subtype.ext
    have hj' : j < 2 := hj
    interval_cases j
    · exact h0.symm
    · exact h1.symm
  rcases e0 with e0 | e0 <;> rcases e1 with e1 | e1
  · exact Or.inl (key _ e0.symm e1.symm)
  · exact Or.inr (Or.inr (Or.inl (key _ e0.symm e1.symm)))
  · exact Or.inr (Or.inl (key _ e0.symm e1.symm))
  · exact Or.inr (Or.inr (Or.inr (key _ e0.symm e1.symm)))

theorem chain42_fin : (univ : Finset (Fin (pathChainDepth chain42 + 1))) = {i0, i1} := by decide

theorem example34_chain42 : pathChainTerm chain42 = 1488 := by
  unfold pathChainTerm
  rw [chain42_family, chain42_univ, sum_insert (by decide), sum_insert (by decide),
    sum_insert (by decide), sum_singleton, chain42_fin]
  simp only [prod_pair (show i0 ≠ i1 by decide)]
  obtain ⟨f1, f2, f3, f4⟩ := example34_F
  rw [f1, f2, f3, f4]
  rw [coeff_of_U11 (P11_11 i0) rfl, coeff_of_U11 (P11_11 i1) rfl, coeff_of_U2 (P2_11 i0) rfl,
    coeff_of_U11 (P2_11 i1) rfl, coeff_of_U11 (P11_2 i0) rfl, coeff_of_U2 (P11_2 i1) rfl,
    coeff_of_U2 (P2_2 i0) rfl, coeff_of_U2 (P2_2 i1) rfl]
  norm_num

def chain43 : PathChain 3 4 := ⟨⟨1, ![4, 3]⟩, by decide⟩
def chain432 : PathChain 3 4 := ⟨⟨2, ![4, 3, 2]⟩, by decide⟩

theorem chain43_family : pathFamilyFactor chain43 = 3 := by decide
theorem chain432_family : pathFamilyFactor chain432 = 6 := by decide

def parts43 (b : Fin 5 → Fin 5) (h : (b 0).val = 0 ∧ ∑ v : Fin 5, v.val * (b v).val = 3) :
    PathPartitionTypes chain43 :=
  fun j => ⟨if j.val = 0 then U1 else b, by
    fin_cases j
    · exact (by decide : (U1 0).val = 0 ∧ ∑ v : Fin 5, v.val * (U1 v).val = 1)
    · exact h⟩

def P43_111 : PathPartitionTypes chain43 := parts43 U111 (by decide)
def P43_21 : PathPartitionTypes chain43 := parts43 U21 (by decide)
def P43_3 : PathPartitionTypes chain43 := parts43 U3 (by decide)

def parts432 (c : Fin 5 → Fin 5) (h : (c 0).val = 0 ∧ ∑ v : Fin 5, v.val * (c v).val = 2) :
    PathPartitionTypes chain432 :=
  fun j => ⟨if j.val < 2 then U1 else c, by
    fin_cases j
    · exact (by decide : (U1 0).val = 0 ∧ ∑ v : Fin 5, v.val * (U1 v).val = 1)
    · exact (by decide : (U1 0).val = 0 ∧ ∑ v : Fin 5, v.val * (U1 v).val = 1)
    · exact h⟩

def P432_11 : PathPartitionTypes chain432 := parts432 U11 (by decide)
def P432_2 : PathPartitionTypes chain432 := parts432 U2 (by decide)

theorem example34_F43 :
    pathF chain43 P43_111 = 248 ∧ pathF chain43 P43_21 = 104 ∧ pathF chain43 P43_3 = 56 := by
  simp only [pathF_eq_fDec]
  decide

theorem example34_F432 : pathF chain432 P432_11 = 64 ∧ pathF chain432 P432_2 = 48 := by
  simp only [pathF_eq_fDec]
  decide

def k0 : Fin (pathChainDepth chain43 + 1) := 0
def k1 : Fin (pathChainDepth chain43 + 1) := 1

theorem chain43_univ : (univ : Finset (PathPartitionTypes chain43)) = {P43_111, P43_21, P43_3} := by
  ext x
  simp only [mem_univ, mem_insert, mem_singleton, true_iff]
  have e0 := pp1_cases (by decide) (x k0)
  have e1 := pp3_cases (by decide) (x k1)
  have key : ∀ P : PathPartitionTypes chain43, (P k1).1 = (x k1).1 → x = P := by
    intro P h1
    funext ⟨j, hj⟩
    apply Subtype.ext
    have hj' : j < 2 := hj
    interval_cases j
    · exact e0.trans (pp1_cases (by decide) (P k0)).symm
    · exact h1.symm
  rcases e1 with e1 | e1 | e1
  · exact Or.inl (key _ e1.symm)
  · exact Or.inr (Or.inl (key _ e1.symm))
  · exact Or.inr (Or.inr (key _ e1.symm))

theorem example34_chain43 : pathChainTerm chain43 = 144 := by
  unfold pathChainTerm
  rw [chain43_family, chain43_univ, sum_insert (by decide), sum_insert (by decide), sum_singleton,
    show (univ : Finset (Fin (pathChainDepth chain43 + 1))) = {k0, k1} by decide]
  simp only [prod_pair (show k0 ≠ k1 by decide)]
  obtain ⟨f1, f2, f3⟩ := example34_F43
  rw [f1, f2, f3, coeff_of_U1 (P43_111 k0) rfl, coeff_of_U111 (P43_111 k1) rfl,
    coeff_of_U1 (P43_21 k0) rfl, coeff_of_U21 (P43_21 k1) rfl,
    coeff_of_U1 (P43_3 k0) rfl, coeff_of_U3 (P43_3 k1) rfl]
  norm_num

def l0 : Fin (pathChainDepth chain432 + 1) := 0
def l1 : Fin (pathChainDepth chain432 + 1) := 1
def l2 : Fin (pathChainDepth chain432 + 1) := 2

theorem chain432_univ : (univ : Finset (PathPartitionTypes chain432)) = {P432_11, P432_2} := by
  ext x
  simp only [mem_univ, mem_insert, mem_singleton, true_iff]
  have e2 := pp2_cases (by decide) (x l2)
  have key : ∀ P : PathPartitionTypes chain432, (P l2).1 = (x l2).1 → x = P := by
    intro P h2
    funext ⟨j, hj⟩
    apply Subtype.ext
    have hj' : j < 3 := hj
    interval_cases j
    · exact (pp1_cases (by decide) (x l0)).trans (pp1_cases (by decide) (P l0)).symm
    · exact (pp1_cases (by decide) (x l1)).trans (pp1_cases (by decide) (P l1)).symm
    · exact h2.symm
  rcases e2 with e2 | e2
  · exact Or.inl (key _ e2.symm)
  · exact Or.inr (key _ e2.symm)

theorem example34_chain432 : pathChainTerm chain432 = 96 := by
  unfold pathChainTerm
  rw [chain432_family, chain432_univ, sum_pair (by decide),
    show (univ : Finset (Fin (pathChainDepth chain432 + 1))) = {l0, l1, l2} by decide]
  simp only [prod_insert (show l0 ∉ ({l1, l2} : Finset _) by decide), prod_pair (show l1 ≠ l2 by decide)]
  obtain ⟨f1, f2⟩ := example34_F432
  rw [f1, f2, coeff_of_U1 (P432_11 l0) rfl, coeff_of_U1 (P432_11 l1) rfl,
    coeff_of_U11 (P432_11 l2) rfl, coeff_of_U1 (P432_2 l0) rfl, coeff_of_U1 (P432_2 l1) rfl,
    coeff_of_U2 (P432_2 l2) rfl]
  norm_num

theorem example34_chains :
    (univ : Finset (PathChain 3 4)) = {chain4, chain42, chain43, chain432} := by
  ext ⟨⟨⟨d, hd⟩, v⟩, h⟩
  simp only [mem_univ, mem_insert, mem_singleton, true_iff]
  have h' := h
  obtain ⟨h0, h2, hlt⟩ := h'
  interval_cases d
  · left
    exact chain_eq_of _ _ h _ fun i => by fin_cases i; exact h0
  · have a1 : (v 1).val < (v 0).val := hlt 0
    have b : 2 ≤ (v 1).val := h2
    change (v 0).val = 4 at h0
    have hv : (v 1).val = 2 ∨ (v 1).val = 3 := by omega
    rcases hv with hv | hv
    · right; left
      exact chain_eq_of _ _ h _ fun i => by fin_cases i; exacts [h0, hv]
    · right; right; left
      exact chain_eq_of _ _ h _ fun i => by fin_cases i; exacts [h0, hv]
  · have a1 : (v 1).val < (v 0).val := hlt 0
    have a2 : (v 2).val < (v 1).val := hlt 1
    have b : 2 ≤ (v 2).val := h2
    change (v 0).val = 4 at h0
    have e1 : (v 1).val = 3 := by omega
    have e2 : (v 2).val = 2 := by omega
    right; right; right
    exact chain_eq_of _ _ h _ fun i => by fin_cases i; exacts [h0, e1, e2]
/-- The right-hand side of Proposition 3.2 at `(3,4)`, from the four chain terms. -/
theorem example34_rhs : pathFormulaRHS 3 4 = (3408 : ℝ) / 1680 := by
  have h : ∑ s : PathChain 3 4, (pathChainTerm s : ℝ) = 3408 := by
    rw [example34_chains, sum_insert (by decide), sum_insert (by decide), sum_insert (by decide),
      sum_singleton, example34_chain4, example34_chain42, example34_chain43, example34_chain432]
    norm_num
  unfold pathFormulaRHS
  rw [show Nat.descFactorial (2 ^ 3) 4 = 1680 from rfl]
  convert congrArg (· / (1680 : ℝ)) h using 3
  congr 1; exact Subsingleton.elim _ _

/-- Proposition 3.2 gives `t_{3,4}(G) = 3408/1680`, the value `example_n3_m4` obtains from Proposition 3.6. -/
theorem example34_tG : tG 3 4 (by norm_num) = (3408 : ℝ) / 1680 := by
  rw [prop_path_formula (by norm_num) (by norm_num), example34_rhs]

/-- The chain terms of Proposition 3.2 for `(n,m) = (3,4)` sum to `3408`. -/
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
