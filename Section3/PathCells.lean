import PathEvent

/-!
# Proposition 3.2: cells and Möbius inversion within each cell

The cells of a path are `S_j \ S_{j+1}` (`j < d`) and `S_d`. Under the rowwise conditions the row tested
at depth `k` separates the cell `k` from every later cell, so the columns are distinct iff they are
distinct within each cell. Möbius inversion is applied in each cell separately: this replaces the sum
over all set partitions of the columns, and the partitions with a block meeting two cells never occur.
-/

noncomputable section

namespace GradientKey.Concrete

open Finset Classical

variable {n m d : ℕ}

/-- `S_{j+1}`, with `S_{d+1} = ∅`. -/
def nextSet (S : Fin (d + 1) → Finset (Fin m)) (j : Fin (d + 1)) : Finset (Fin m) :=
  if h : j.val + 1 < d + 1 then S ⟨j.val + 1, h⟩ else ∅

/-- The cell `S_j \ S_{j+1}`; the last cell is `S_d`. -/
def cell (S : Fin (d + 1) → Finset (Fin m)) (j : Fin (d + 1)) : Finset (Fin m) :=
  S j \ nextSet S j

/-- An enumeration of the cell `j`. -/
def cellEmb (S : Fin (d + 1) → Finset (Fin m)) (j : Fin (d + 1)) :
    Fin (cell S j).card → Fin m := fun t => ((cell S j).equivFin.symm t).1

theorem cellEmb_injective (S : Fin (d + 1) → Finset (Fin m)) (j : Fin (d + 1)) :
    Function.Injective (cellEmb S j) := by
  intro a b h
  exact (cell S j).equivFin.symm.injective (Subtype.ext h)

theorem cellEmb_mem (S : Fin (d + 1) → Finset (Fin m)) (j : Fin (d + 1)) (t : Fin (cell S j).card) :
    cellEmb S j t ∈ cell S j := ((cell S j).equivFin.symm t).2

theorem cellEmb_surj (S : Fin (d + 1) → Finset (Fin m)) (j : Fin (d + 1)) (x : Fin m)
    (hx : x ∈ cell S j) : ∃ t, cellEmb S j t = x :=
  ⟨(cell S j).equivFin ⟨x, hx⟩, by simp [cellEmb]⟩

/-- Every column lies in a cell. -/
theorem exists_cell (S : Fin (d + 1) → Finset (Fin m)) (h0 : S 0 = univ) (x : Fin m) :
    ∃ k, x ∈ cell S k := by
  let F := univ.filter (fun i : Fin (d + 1) => x ∈ S i)
  have hne : F.Nonempty := ⟨0, by simp [F, h0]⟩
  refine ⟨F.max' hne, ?_⟩
  have hmem := (mem_filter.mp (F.max'_mem hne)).2
  rw [cell, mem_sdiff]
  refine ⟨hmem, ?_⟩
  unfold nextSet
  split_ifs with hlt
  · intro hx
    have hle : (⟨(F.max' hne).val + 1, hlt⟩ : Fin (d + 1)) ≤ F.max' hne :=
      F.le_max' _ (by simp [F, hx])
    have := Fin.le_iff_val_le_val.mp hle
    simp at this
  · simp

section rowwise

variable {A : Table n m} {S : Fin (d + 1) → Finset (Fin m)} {j₀ : Fin m} {rho : Fin d ↪ Fin n}

theorem step_subset_of_rowwise (h : fixedPathRowwise S j₀ rho A) (j : Fin d) :
    S j.succ ⊆ S j.castSucc := by
  rw [(h (rho j) j).1 rfl]
  exact filter_subset _ _

theorem subset_of_rowwise_aux (h : fixedPathRowwise S j₀ rho A) :
    ∀ (t : ℕ) (k : Fin (d + 1)) (hk : k.val + t < d + 1), S ⟨k.val + t, hk⟩ ⊆ S k
  | 0, k, _ => Finset.Subset.refl _
  | t + 1, k, hk => by
    have hj : k.val + t < d := by omega
    exact (step_subset_of_rowwise h ⟨k.val + t, hj⟩).trans
      (subset_of_rowwise_aux h t k (by omega))

/-- Under the rowwise conditions the candidate sets are nested. -/
theorem subset_of_rowwise (h : fixedPathRowwise S j₀ rho A) {k l : Fin (d + 1)}
    (hkl : k.val ≤ l.val) : S l ⊆ S k := by
  have := subset_of_rowwise_aux h (l.val - k.val) k (by omega)
  have e : (⟨k.val + (l.val - k.val), by omega⟩ : Fin (d + 1)) = l := Fin.ext (by simp; omega)
  rwa [e] at this

/-- The row tested at depth `k` separates the cell `k` from every later cell. -/
theorem cell_sep (h : fixedPathRowwise S j₀ rho A) {k l : Fin (d + 1)} (hkl : k.val < l.val)
    {x y : Fin m} (hx : x ∈ cell S k) (hy : y ∈ cell S l) : ∃ r, A r x ≠ A r y := by
  have hkd : k.val < d := by have := l.isLt; omega
  set kd : Fin d := ⟨k.val, hkd⟩
  have hsplit := (h (rho kd) kd).1 rfl
  have hxS : x ∈ S kd.castSucc := (mem_sdiff.mp hx).1
  have hxn : x ∉ S kd.succ := by
    have := (mem_sdiff.mp hx).2
    unfold nextSet at this
    rw [dif_pos (by omega)] at this
    exact this
  have hyS : y ∈ S kd.succ :=
    subset_of_rowwise h (k := kd.succ) (l := l) (by simp [kd]; omega) (mem_sdiff.mp hy).1
  rw [hsplit] at hxn hyS
  simp only [mem_filter] at hxn hyS
  refine ⟨rho kd, fun hxy => hxn ⟨hxS, ?_⟩⟩
  rw [hxy]
  exact hyS.2

/-- The columns of a table satisfying the rowwise conditions are distinct iff they are distinct
within each cell. -/
theorem distinct_iff_cells (h : fixedPathRowwise S j₀ rho A) (h0 : S 0 = univ) :
    DistinctColumns A ↔ ∀ j, Function.Injective
      (fun t : Fin (cell S j).card => fun i : Fin n => A i (cellEmb S j t)) := by
  constructor
  · intro hd j a b hab
    exact cellEmb_injective S j (hd hab)
  · intro hc x y hxy
    obtain ⟨k, hx⟩ := exists_cell S h0 x
    obtain ⟨l, hy⟩ := exists_cell S h0 y
    rcases lt_trichotomy k.val l.val with hlt | heq | hgt
    · obtain ⟨r, hr⟩ := cell_sep h hlt hx hy
      exact absurd (congrFun hxy r) hr
    · have hkl : k = l := Fin.ext heq
      subst hkl
      obtain ⟨a, rfl⟩ := cellEmb_surj S k x hx
      obtain ⟨b, rfl⟩ := cellEmb_surj S k y hy
      exact congrArg _ (hc k hxy)
    · obtain ⟨r, hr⟩ := cell_sep h hgt hy hx
      exact absurd (congrFun hxy r).symm hr

/-- Möbius inversion in each cell. -/
theorem distinct_indicator_cells (h : fixedPathRowwise S j₀ rho A) (h0 : S 0 = univ) :
    (if DistinctColumns A then (1 : ℤ) else 0) =
      ∑ ps : ((j : Fin (d + 1)) → OrderedFinpartition (cell S j).card),
        (∏ j, mu (ps j)) *
          (if ∀ i : Fin n, ∀ j, ConstOn (ps j) (fun t => A i (cellEmb S j t)) then 1 else 0) := by
  set col : (j : Fin (d + 1)) → Fin (cell S j).card → Fin n → Bool :=
    fun j t i => A i (cellEmb S j t)
  have hprod : (if DistinctColumns A then (1 : ℤ) else 0) =
      ∏ j, (if Function.Injective (col j) then (1 : ℤ) else 0) := by
    by_cases hd : DistinctColumns A
    · rw [if_pos hd]
      symm
      apply prod_eq_one
      intro j _
      rw [if_pos ((distinct_iff_cells h h0).mp hd j)]
    · rw [if_neg hd]
      symm
      obtain ⟨j, hj⟩ : ∃ j, ¬ Function.Injective (col j) := by
        by_contra hc
        push_neg at hc
        exact hd ((distinct_iff_cells h h0).mpr hc)
      exact prod_eq_zero (mem_univ j) (if_neg hj)
  rw [hprod, Finset.prod_congr rfl (fun j _ => (mobius_injective _ (col j)).symm), Fintype.prod_sum]
  apply sum_congr rfl
  intro ps _
  have hrow : ∀ j, ConstOn (ps j) (col j) ↔ ∀ i : Fin n, ConstOn (ps j) (fun t => A i (cellEmb S j t)) :=
    fun j => constOn_columns_iff_rows (ps j) (fun i t => A i (cellEmb S j t))
  by_cases hall : ∀ j, ConstOn (ps j) (col j)
  · rw [prod_congr rfl (fun j _ => if_pos (hall j)), if_pos (fun i j => (hrow j).mp (hall j) i),
      mul_one]
  · obtain ⟨j, hj⟩ := not_forall.mp hall
    rw [prod_eq_zero (mem_univ j) (if_neg hj), if_neg, mul_zero]
    intro hrows
    exact hj ((hrow j).mpr (fun i => hrows i j))

end rowwise

/-- **Path count by cells.** The number of valid tables whose column `j₀` has candidate sets
`S₀,…,S_d` is a sum over schedules and over set partitions of the cells. -/
theorem card_path_cells (hn : 0 < n) (S : Fin (d + 1) → Finset (Fin m)) (j₀ : Fin m)
    (h0 : S 0 = univ) (h2 : ∀ j : Fin d, 2 ≤ (S j.castSucc).card) :
    ((univ.filter (fun A : ValidTable n m =>
        ∀ i : Fin (d + 1), candidateAt A.1 j₀ hn i = S i)).card : ℤ) =
      ∑ rho : Fin d ↪ Fin n,
        ∑ ps : ((j : Fin (d + 1)) → OrderedFinpartition (cell S j).card),
          (∏ j, mu (ps j)) * ∏ i : Fin n,
            ((univ.filter (fun row : Row m => fixedPathRowAdmissible S j₀ rho i row ∧
              ∀ j, ConstOn (ps j) (fun t => row (cellEmb S j t)))).card : ℤ) := by
  have hv := card_valid_filter (n := n) (m := m)
    (fun A => ∀ i : Fin (d + 1), candidateAt A j₀ hn i = S i)
  beta_reduce at hv
  refine Eq.trans (b := ∑ A : Table n m,
    if (∀ i : Fin (d + 1), candidateAt A j₀ hn i = S i) ∧ DistinctColumns A then (1 : ℤ) else 0)
    (by convert hv using 3; congr 1) ?_
  have hpt : ∀ A : Table n m,
      (if (∀ i : Fin (d + 1), candidateAt A j₀ hn i = S i) ∧ DistinctColumns A then (1 : ℤ) else 0) =
        ∑ rho : Fin d ↪ Fin n,
          if fixedPathRowwise S j₀ rho A ∧ DistinctColumns A then (1 : ℤ) else 0 := by
    intro A
    by_cases hA : DistinctColumns A
    · simp only [and_iff_left hA]
      exact path_indicator_eq_sum A hA hn S j₀ h0 h2
    · simp [hA]
  rw [Finset.sum_congr rfl (fun A _ => hpt A), Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro rho _
  set P : (ps : (j : Fin (d + 1)) → OrderedFinpartition (cell S j).card) → Fin n → Row m → Prop :=
    fun ps i row => fixedPathRowAdmissible S j₀ rho i row ∧
      ∀ j, ConstOn (ps j) (fun t => row (cellEmb S j t))
  have hA : ∀ A : Table n m,
      (if fixedPathRowwise S j₀ rho A ∧ DistinctColumns A then (1 : ℤ) else 0) =
        ∑ ps : ((j : Fin (d + 1)) → OrderedFinpartition (cell S j).card),
          (∏ j, mu (ps j)) * (if ∀ i, P ps i (A i) then 1 else 0) := by
    intro A
    by_cases hr : fixedPathRowwise S j₀ rho A
    · simp only [hr, true_and]
      rw [distinct_indicator_cells hr h0]
      apply sum_congr rfl
      intro ps _
      congr 1
      apply if_congr _ rfl rfl
      exact ⟨fun hc i => ⟨hr i, fun j => hc i j⟩, fun hc i j => (hc i).2 j⟩
    · simp only [hr, false_and, if_false]
      symm
      apply sum_eq_zero
      intro ps _
      rw [if_neg, mul_zero]
      exact fun hc => hr (fun i => (hc i).1)
  rw [Finset.sum_congr rfl (fun A _ => hA A), Finset.sum_comm]
  apply sum_congr rfl
  intro ps _
  rw [← Finset.mul_sum, Finset.sum_boole]
  congr 1
  have hc := card_row_constraints_filter (n := n) (m := m) (P ps)
  have hc' := congrArg (fun x : ℕ => (x : ℤ)) hc
  simp only [Nat.cast_prod] at hc'
  convert hc' using 5

end GradientKey.Concrete
