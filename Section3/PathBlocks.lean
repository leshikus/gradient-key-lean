import PathCells

/-!
# Proposition 3.1: rows constant on blocks are assignments

Let the columns be enumerated as `E : (Σ b : ι, Fin (size b)) ≃ Fin m`, block `b` having `size b ≥ 1`
columns and lying in the cell `cellOf b`, so that `x ∈ S_i ↔ i ≤ cellOf (block of x)`. A row constant on
every block is an assignment `ι → Bool` (one bit per block). The number of ones of such a row on `S_i`
is the weighted number of blocks with bit `1` in the cells `≥ i`, and the rowwise path conditions become
the conditions `blkAdm` on assignments. Hence the two counts agree (`card_rows_eq_blk`).
-/

noncomputable section

namespace GradientKey.Concrete

open Finset Classical

variable {n m d : ℕ}

section general

variable {ι : Type*} [Fintype ι] (size : ι → ℕ) (cellOf : ι → Fin (d + 1))

/-- The weighted number of blocks with bit `1` in the cells `≥ i`: the ones of the row on `S_i`. -/
def blkOnes (bits : ι → Bool) (i : Fin (d + 1)) : ℕ :=
  ∑ b, if i ≤ cellOf b ∧ bits b = true then size b else 0

/-- The quality of the row on `S_i`, of size `sz i`. -/
def blkQual (sz : Fin (d + 1) → ℕ) (bits : ι → Bool) (i : Fin (d + 1)) : ℕ :=
  min (blkOnes size cellOf bits i) (sz i - blkOnes size cellOf bits i)

/-- The rowwise path conditions for row `i`, in terms of the bits of the blocks. -/
def blkAdm (sz : Fin (d + 1) → ℕ) (q : Fin d → ℕ) (rho : Fin d ↪ Fin n) (i : Fin n)
    (bits : ι → Bool) : Prop :=
  ∀ j : Fin d,
    (rho j = i → ∃ bb : Bool, ∀ b, (cellOf b = j.castSucc → bits b = !bb) ∧
        (j.castSucc < cellOf b → bits b = bb)) ∧
    (rho j ≠ i → if i < rho j then blkQual size cellOf sz bits j.castSucc < q j
      else blkQual size cellOf sz bits j.castSucc ≤ q j)

end general

section enumeration

variable {ι : Type*} [Fintype ι] {size : ι → ℕ} {cellOf : ι → Fin (d + 1)}
  {E : (Σ b : ι, Fin (size b)) ≃ Fin m} {S : Fin (d + 1) → Finset (Fin m)}

/-- The row of an assignment. -/
def rowOf (E : (Σ b : ι, Fin (size b)) ≃ Fin m) (bits : ι → Bool) : Row m :=
  fun x => bits (E.symm x).1

theorem rowOf_E (bits : ι → Bool) (b : ι) (r : Fin (size b)) : rowOf E bits (E ⟨b, r⟩) = bits b := by
  simp [rowOf]

theorem ones_rowOf (hS : ∀ i x, x ∈ S i ↔ i ≤ cellOf (E.symm x).1) (bits : ι → Bool)
    (i : Fin (d + 1)) :
    ((S i).filter (fun x => rowOf E bits x = true)).card = blkOnes size cellOf bits i := by
  have hSi : S i = univ.filter (fun x => i ≤ cellOf (E.symm x).1) := by
    ext x; simp [hS i x]
  rw [hSi, filter_filter, card_filter]
  rw [← E.sum_comp, Fintype.sum_sigma]
  unfold blkOnes
  apply sum_congr rfl
  intro b _
  simp only [Equiv.symm_apply_apply, rowOf]
  rw [sum_const, card_univ, Fintype.card_fin, smul_eq_mul]
  split_ifs <;> simp

theorem rq_rowOf (hS : ∀ i x, x ∈ S i ↔ i ≤ cellOf (E.symm x).1) (bits : ι → Bool)
    (i : Fin (d + 1)) :
    rq (S i) (rowOf E bits) = blkQual size cellOf (fun i => (S i).card) bits i := by
  unfold rq blkQual
  rw [ones_rowOf hS]
  congr 1
  have h := card_filter_add_card_filter_not (s := S i) (fun x => rowOf E bits x = true)
  rw [ones_rowOf hS] at h
  have he : (S i).filter (fun x => rowOf E bits x = false) =
      (S i).filter (fun x => ¬ rowOf E bits x = true) := by
    apply filter_congr; intro x _; cases rowOf E bits x <;> simp
  rw [he]
  beta_reduce
  omega

theorem split_rowOf (hS : ∀ i x, x ∈ S i ↔ i ≤ cellOf (E.symm x).1) (hsize : ∀ b, 0 < size b)
    (j₀ : Fin m) (hj₀ : cellOf (E.symm j₀).1 = Fin.last d) (bits : ι → Bool) (j : Fin d) :
    S j.succ = (S j.castSucc).filter (fun k => rowOf E bits k = rowOf E bits j₀) ↔
      ∃ bb : Bool, ∀ b, (cellOf b = j.castSucc → bits b = !bb) ∧
        (j.castSucc < cellOf b → bits b = bb) := by
  have hlast : j.castSucc < cellOf (E.symm j₀).1 := by
    rw [hj₀]; exact Fin.castSucc_lt_last j
  constructor
  · intro h
    refine ⟨rowOf E bits j₀, fun b => ⟨fun hb => ?_, fun hb => ?_⟩⟩
    · have hx : E ⟨b, ⟨0, hsize b⟩⟩ ∈ S j.castSucc := by
        rw [hS]; simp [hb]
      have hx' : E ⟨b, ⟨0, hsize b⟩⟩ ∉ S j.succ := by
        rw [hS]; simp [hb, Fin.succ_le_castSucc_iff]
      rw [h, mem_filter] at hx'
      rw [rowOf_E] at hx'
      have : bits b ≠ rowOf E bits j₀ := fun he => hx' ⟨hx, he⟩
      cases hbb : bits b <;> cases hr : rowOf E bits j₀ <;> simp_all
    · have hx : E ⟨b, ⟨0, hsize b⟩⟩ ∈ S j.succ := by
        rw [hS]; simp only [Equiv.symm_apply_apply]
        exact Fin.castSucc_lt_iff_succ_le.mp hb
      rw [h, mem_filter, rowOf_E] at hx
      exact hx.2
  · rintro ⟨bb, hbb⟩
    have hj0 : rowOf E bits j₀ = bb := (hbb _).2 hlast
    ext x
    rw [mem_filter, hj0, hS, hS]
    set c := cellOf (E.symm x).1
    have hrow : rowOf E bits x = bits (E.symm x).1 := rfl
    rw [hrow]
    constructor
    · intro hc
      have hlt : j.castSucc < c := Fin.castSucc_lt_iff_succ_le.mpr hc
      exact ⟨hlt.le, (hbb _).2 hlt⟩
    · rintro ⟨hc, hb⟩
      rcases hc.lt_or_eq with hlt | heq
      · exact Fin.castSucc_lt_iff_succ_le.mp hlt
      · have := (hbb _).1 heq.symm
        rw [this] at hb
        cases bb <;> simp at hb

theorem adm_rowOf_iff (hS : ∀ i x, x ∈ S i ↔ i ≤ cellOf (E.symm x).1) (hsize : ∀ b, 0 < size b)
    (j₀ : Fin m) (hj₀ : cellOf (E.symm j₀).1 = Fin.last d) (rho : Fin d ↪ Fin n) (i : Fin n)
    (bits : ι → Bool) :
    fixedPathRowAdmissible S j₀ rho i (rowOf E bits) ↔
      blkAdm size cellOf (fun i => (S i).card) (fixedPathQuality S) rho i bits := by
  unfold fixedPathRowAdmissible blkAdm
  apply forall_congr'
  intro j
  rw [split_rowOf hS hsize j₀ hj₀ bits j, rq_rowOf hS bits]

/-- **Rows constant on blocks = assignments.** -/
theorem card_rows_eq_blk (hS : ∀ i x, x ∈ S i ↔ i ≤ cellOf (E.symm x).1) (hsize : ∀ b, 0 < size b)
    (j₀ : Fin m) (hj₀ : cellOf (E.symm j₀).1 = Fin.last d) (rho : Fin d ↪ Fin n) (i : Fin n) :
    (univ.filter (fun row : Row m => fixedPathRowAdmissible S j₀ rho i row ∧
        ∀ b (r r' : Fin (size b)), row (E ⟨b, r⟩) = row (E ⟨b, r'⟩))).card =
      (univ.filter (fun bits : ι → Bool =>
        blkAdm size cellOf (fun i => (S i).card) (fixedPathQuality S) rho i bits)).card := by
  symm
  apply Finset.card_bij' (fun bits _ => rowOf E bits) (fun row _ => fun b => row (E ⟨b, ⟨0, hsize b⟩⟩))
  · intro bits hb
    rw [mem_filter] at hb ⊢
    refine ⟨mem_univ _, (adm_rowOf_iff hS hsize j₀ hj₀ rho i bits).mpr hb.2, ?_⟩
    intro b r r'
    rw [rowOf_E, rowOf_E]
  · intro row hr
    rw [mem_filter] at hr ⊢
    refine ⟨mem_univ _, ?_⟩
    have hrow : rowOf E (fun b => row (E ⟨b, ⟨0, hsize b⟩⟩)) = row := by
      funext x
      unfold rowOf
      have hx := E.apply_symm_apply x
      conv_rhs => rw [← hx]
      exact hr.2.2 _ _ _
    rw [← adm_rowOf_iff hS hsize j₀ hj₀ rho i, hrow]
    exact hr.2.1
  · intro bits _
    funext b
    exact rowOf_E bits b _
  · intro row hr
    rw [mem_filter] at hr
    funext x
    unfold rowOf
    have hx := E.apply_symm_apply x
    conv_rhs => rw [← hx]
    exact hr.2.2 _ _ _

end enumeration

end GradientKey.Concrete
