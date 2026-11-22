import PathBlocks
import PathCoeff2

/-!
# Proposition 3.1: the row counts depend only on the block sizes

For nested candidate sets `S` with `S₀ = univ` and `j₀ ∈ S_d`, and set partitions `ps j` of the cells,
the columns are enumerated by (cell, block, position in block). By `card_rows_eq_blk` the number of
admissible rows constant on the blocks is a count of assignments to the blocks. That count is unchanged
under relabelling the blocks within each cell by their sizes, so it depends only on the types
`typeVec (ps j)` (`rowcount_eq_cntU`).
-/

noncomputable section

namespace GradientKey.Concrete

open Finset Classical

variable {n m d : ℕ}

section family

variable {S : Fin (d + 1) → Finset (Fin m)}

theorem subset_of_nest_aux (hnest : ∀ j : Fin d, S j.succ ⊆ S j.castSucc) :
    ∀ (t : ℕ) (k : Fin (d + 1)) (hk : k.val + t < d + 1), S ⟨k.val + t, hk⟩ ⊆ S k
  | 0, k, _ => Finset.Subset.refl _
  | t + 1, k, hk => by
    have hj : k.val + t < d := by omega
    exact (hnest ⟨k.val + t, hj⟩).trans (subset_of_nest_aux hnest t k (by omega))

theorem subset_of_nest (hnest : ∀ j : Fin d, S j.succ ⊆ S j.castSucc) {k l : Fin (d + 1)}
    (hkl : k.val ≤ l.val) : S l ⊆ S k := by
  have := subset_of_nest_aux hnest (l.val - k.val) k (by omega)
  have e : (⟨k.val + (l.val - k.val), by omega⟩ : Fin (d + 1)) = l := Fin.ext (by simp; omega)
  rwa [e] at this

/-- A column of the cell `j` lies in `S_i` exactly for `i ≤ j`. -/
theorem mem_S_of_cell (hnest : ∀ j : Fin d, S j.succ ⊆ S j.castSucc) {x : Fin m} {j : Fin (d + 1)}
    (hx : x ∈ cell S j) (i : Fin (d + 1)) : x ∈ S i ↔ i ≤ j := by
  rw [cell, mem_sdiff] at hx
  constructor
  · intro hi
    by_contra hlt
    push_neg at hlt
    have hj1 : j.val + 1 < d + 1 := by have := i.isLt; omega
    apply hx.2
    unfold nextSet
    rw [dif_pos hj1]
    exact subset_of_nest hnest (k := ⟨j.val + 1, hj1⟩) (l := i) (by simp; omega) hi
  · intro hi
    exact subset_of_nest hnest (Fin.le_iff_val_le_val.mp hi) hx.1

theorem cell_unique (hnest : ∀ j : Fin d, S j.succ ⊆ S j.castSucc) {x : Fin m} {j j' : Fin (d + 1)}
    (hx : x ∈ cell S j) (hx' : x ∈ cell S j') : j = j' := by
  have h1 := (mem_S_of_cell hnest hx j').mp (cell_subset hx')
  have h2 := (mem_S_of_cell hnest hx' j).mp (cell_subset hx)
  exact le_antisymm h2 h1
where
  cell_subset {y : Fin m} {k : Fin (d + 1)} (hy : y ∈ cell S k) : y ∈ S k :=
    (mem_sdiff.mp hy).1

/-- The columns, enumerated by cells. -/
def cellsEquiv (h0 : S 0 = univ) (hnest : ∀ j : Fin d, S j.succ ⊆ S j.castSucc) :
    (Σ j : Fin (d + 1), Fin (cell S j).card) ≃ Fin m :=
  Equiv.ofBijective (fun p => cellEmb S p.1 p.2) ⟨by
    rintro ⟨j, t⟩ ⟨j', t'⟩ h
    simp only at h
    have hj : j = j' := cell_unique hnest (cellEmb_mem S j t) (by rw [h]; exact cellEmb_mem S j' t')
    subst hj
    have := cellEmb_injective S j h
    subst this
    rfl, by
    intro x
    obtain ⟨k, hk⟩ := exists_cell S h0 x
    obtain ⟨t, ht⟩ := cellEmb_surj S k x hk
    exact ⟨⟨k, t⟩, ht⟩⟩

/-- The positions of `Fin a`, enumerated by the blocks of a set partition. -/
def blkEquiv {a : ℕ} (c : OrderedFinpartition a) : (Σ k : Fin c.length, Fin (c.partSize k)) ≃ Fin a :=
  Equiv.ofBijective (fun p => c.emb p.1 p.2) ⟨c.emb_injective, by
    intro x
    obtain ⟨k, r, hr⟩ := c.cover x
    exact ⟨⟨k, r⟩, hr⟩⟩

/-- The columns, enumerated by (cell, block, position). -/
def Etot (h0 : S 0 = univ) (hnest : ∀ j : Fin d, S j.succ ⊆ S j.castSucc)
    (ps : (j : Fin (d + 1)) → OrderedFinpartition (cell S j).card) :
    (Σ b : (Σ j : Fin (d + 1), Fin (ps j).length), Fin ((ps b.1).partSize b.2)) ≃ Fin m :=
  (Equiv.sigmaAssoc (fun j (k : Fin (ps j).length) => Fin ((ps j).partSize k))).trans
    ((Equiv.sigmaCongrRight (fun j => blkEquiv (ps j))).trans (cellsEquiv h0 hnest))

theorem Etot_apply (h0 : S 0 = univ) (hnest : ∀ j : Fin d, S j.succ ⊆ S j.castSucc)
    (ps : (j : Fin (d + 1)) → OrderedFinpartition (cell S j).card) (j : Fin (d + 1))
    (k : Fin (ps j).length) (r : Fin ((ps j).partSize k)) :
    Etot h0 hnest ps ⟨⟨j, k⟩, r⟩ = cellEmb S j ((ps j).emb k r) := rfl

theorem Etot_hS (h0 : S 0 = univ) (hnest : ∀ j : Fin d, S j.succ ⊆ S j.castSucc)
    (ps : (j : Fin (d + 1)) → OrderedFinpartition (cell S j).card) (i : Fin (d + 1)) (x : Fin m) :
    x ∈ S i ↔ i ≤ ((Etot h0 hnest ps).symm x).1.1 := by
  rcases hp : (Etot h0 hnest ps).symm x with ⟨⟨j, k⟩, r⟩
  have hx : x = cellEmb S j ((ps j).emb k r) := by
    rw [← (Etot h0 hnest ps).apply_symm_apply x, hp]
    rfl
  rw [hx]
  exact mem_S_of_cell hnest (cellEmb_mem S j _) i

theorem constOn_iff_Etot (h0 : S 0 = univ) (hnest : ∀ j : Fin d, S j.succ ⊆ S j.castSucc)
    (ps : (j : Fin (d + 1)) → OrderedFinpartition (cell S j).card) (row : Row m) :
    (∀ j, ConstOn (ps j) (fun t => row (cellEmb S j t))) ↔
      ∀ b (r r' : Fin ((ps b.1).partSize b.2)),
        row (Etot h0 hnest ps ⟨b, r⟩) = row (Etot h0 hnest ps ⟨b, r'⟩) := by
  constructor
  · rintro h ⟨j, k⟩ r r'
    exact h j k r r'
  · intro h j k r r'
    exact h ⟨j, k⟩ r r'

/-- The row count as a count of assignments to the blocks of the cell partitions. -/
theorem rowcount_eq_blk (h0 : S 0 = univ) (hnest : ∀ j : Fin d, S j.succ ⊆ S j.castSucc)
    (j₀ : Fin m) (hj₀ : j₀ ∈ S (Fin.last d))
    (ps : (j : Fin (d + 1)) → OrderedFinpartition (cell S j).card) (rho : Fin d ↪ Fin n) (i : Fin n) :
    (univ.filter (fun row : Row m => fixedPathRowAdmissible S j₀ rho i row ∧
        ∀ j, ConstOn (ps j) (fun t => row (cellEmb S j t)))).card =
      (univ.filter (fun bits : (Σ j : Fin (d + 1), Fin (ps j).length) → Bool =>
        blkAdm (fun b : (Σ j : Fin (d + 1), Fin (ps j).length) => (ps b.1).partSize b.2)
          (fun b : (Σ j : Fin (d + 1), Fin (ps j).length) => b.1) (fun i => (S i).card)
          (fixedPathQuality S) rho i bits)).card := by
  have hS := Etot_hS h0 hnest ps
  have hlast : ((Etot h0 hnest ps).symm j₀).1.1 = Fin.last d :=
    Fin.last_le_iff.mp ((hS _ j₀).mp hj₀)
  have hcongr : univ.filter (fun row : Row m => fixedPathRowAdmissible S j₀ rho i row ∧
        ∀ j, ConstOn (ps j) (fun t => row (cellEmb S j t))) =
      univ.filter (fun row : Row m => fixedPathRowAdmissible S j₀ rho i row ∧
        ∀ b (r r' : Fin ((ps b.1).partSize b.2)),
          row (Etot h0 hnest ps ⟨b, r⟩) = row (Etot h0 hnest ps ⟨b, r'⟩)) := by
    apply filter_congr
    intro row _
    rw [constOn_iff_Etot]
  rw [hcongr]
  convert card_rows_eq_blk (cellOf := fun b : (Σ j : Fin (d + 1), Fin (ps j).length) => b.1) hS
    (fun b : (Σ j : Fin (d + 1), Fin (ps j).length) => (ps b.1).partSize_pos b.2) j₀ hlast rho i
    using 3
  congr 1
  exact Subsingleton.elim _ _

end family

/-! ### Relabelling blocks -/

/-- Counting a filter does not depend on the instances. -/
theorem card_filter_inst {α : Type*} {i1 : Fintype α} {i2 : Fintype α} (p : α → Prop)
    {d1 : DecidablePred p} {d2 : DecidablePred p} :
    (@Finset.filter α p d1 (@univ α i1)).card = (@Finset.filter α p d2 (@univ α i2)).card := by
  rw [Subsingleton.elim i1 i2, Subsingleton.elim d1 d2]

theorem blkOnes_comp {ι ι' : Type*} [Fintype ι] [Fintype ι'] (e : ι' ≃ ι) (size : ι → ℕ)
    (cellOf : ι → Fin (d + 1)) (bits : ι → Bool) (i : Fin (d + 1)) :
    blkOnes (size ∘ e) (cellOf ∘ e) (bits ∘ e) i = blkOnes size cellOf bits i := by
  unfold blkOnes
  exact e.sum_comp (fun b => if i ≤ cellOf b ∧ bits b = true then size b else 0)

theorem blkAdm_comp {ι ι' : Type*} [Fintype ι] [Fintype ι'] (e : ι' ≃ ι) (size : ι → ℕ)
    (cellOf : ι → Fin (d + 1)) (sz : Fin (d + 1) → ℕ) (q : Fin d → ℕ) (rho : Fin d ↪ Fin n)
    (i : Fin n) (bits : ι → Bool) :
    blkAdm (size ∘ e) (cellOf ∘ e) sz q rho i (bits ∘ e) ↔ blkAdm size cellOf sz q rho i bits := by
  unfold blkAdm blkQual
  simp only [blkOnes_comp]
  apply forall_congr'
  intro j
  apply and_congr_left'
  apply imp_congr_right
  intro _
  apply exists_congr
  intro bb
  exact e.forall_congr (fun {_} => Iff.rfl)

/-- The count of admissible assignments does not depend on the labels of the blocks. -/
theorem card_blkAdm_equiv {ι ι' : Type*} [Fintype ι] [Fintype ι'] (e : ι' ≃ ι) (size : ι → ℕ)
    (cellOf : ι → Fin (d + 1)) (sz : Fin (d + 1) → ℕ) (q : Fin d → ℕ) (rho : Fin d ↪ Fin n)
    (i : Fin n) :
    (univ.filter (fun bits : ι → Bool => blkAdm size cellOf sz q rho i bits)).card =
      (univ.filter (fun bits : ι' → Bool =>
        blkAdm (size ∘ e) (cellOf ∘ e) sz q rho i bits)).card := by
  apply Finset.card_bij' (fun bits _ => bits ∘ e) (fun bits _ => bits ∘ e.symm)
  · intro bits hb
    rw [mem_filter] at hb ⊢
    exact ⟨mem_univ _, (blkAdm_comp e size cellOf sz q rho i bits).mpr hb.2⟩
  · intro bits hb
    rw [mem_filter] at hb ⊢
    refine ⟨mem_univ _, ?_⟩
    rw [← blkAdm_comp e]
    have : (bits ∘ e.symm) ∘ e = bits := by funext b; simp
    rw [this]
    exact hb.2
  · intro bits _; funext b; simp
  · intro bits _; funext b; simp

/-- The size of a block, as an element of `Fin B`. -/
def typeFun {a : ℕ} (B : ℕ) (hB : a < B) (c : OrderedFinpartition a) (k : Fin c.length) : Fin B :=
  ⟨c.partSize k, by have := c.partSize_le k; omega⟩

theorem typeFun_card {a : ℕ} (B : ℕ) (hB : a < B) (c : OrderedFinpartition a) (v : Fin B) :
    Fintype.card {k // typeFun B hB c k = v} = typeVec c v.val := by
  rw [Fintype.card_subtype]
  unfold typeVec
  congr 1

/-- The blocks of a set partition, labelled by (size, index among the blocks of that size). -/
def typeEquiv {a : ℕ} (B : ℕ) (hB : a < B) (c : OrderedFinpartition a) :
    (Σ v : Fin B, Fin (typeVec c v.val)) ≃ Fin c.length :=
  (Equiv.sigmaCongrRight (fun v => (Fintype.equivFinOfCardEq (typeFun_card B hB c v)).symm)).trans
    (Equiv.sigmaFiberEquiv (typeFun B hB c))

theorem typeEquiv_size {a : ℕ} (B : ℕ) (hB : a < B) (c : OrderedFinpartition a) (v : Fin B)
    (t : Fin (typeVec c v.val)) : c.partSize (typeEquiv B hB c ⟨v, t⟩) = v.val := by
  unfold typeEquiv
  simp only [Equiv.trans_apply, Equiv.sigmaCongrRight_apply, Equiv.sigmaFiberEquiv_apply]
  exact congrArg Fin.val ((Fintype.equivFinOfCardEq (typeFun_card B hB c v)).symm t).2

/-- The count of admissible assignments to blocks labelled by sizes, for multiplicities `U`. -/
def cntU (B : ℕ) (U : Fin (d + 1) → Fin B → ℕ) (sz : Fin (d + 1) → ℕ) (q : Fin d → ℕ)
    (rho : Fin d ↪ Fin n) (i : Fin n) : ℕ :=
  Fintype.card {bits : (Σ j : Fin (d + 1), Σ v : Fin B, Fin (U j v)) → Bool //
    blkAdm (fun b : (Σ j : Fin (d + 1), Σ v : Fin B, Fin (U j v)) => b.2.1.val)
      (fun b : (Σ j : Fin (d + 1), Σ v : Fin B, Fin (U j v)) => b.1) sz q rho i bits}

/-- **The row count depends only on the types of the cell partitions.** -/
theorem rowcount_eq_cntU {S : Fin (d + 1) → Finset (Fin m)} (h0 : S 0 = univ)
    (hnest : ∀ j : Fin d, S j.succ ⊆ S j.castSucc) (j₀ : Fin m) (hj₀ : j₀ ∈ S (Fin.last d))
    (B : ℕ) (hB : m < B)
    (ps : (j : Fin (d + 1)) → OrderedFinpartition (cell S j).card) (rho : Fin d ↪ Fin n) (i : Fin n) :
    (univ.filter (fun row : Row m => fixedPathRowAdmissible S j₀ rho i row ∧
        ∀ j, ConstOn (ps j) (fun t => row (cellEmb S j t)))).card =
      cntU B (fun j v => typeVec (ps j) v.val) (fun i => (S i).card) (fixedPathQuality S) rho i := by
  rw [rowcount_eq_blk h0 hnest j₀ hj₀ ps rho i]
  have hcard : ∀ j, (cell S j).card < B := fun j =>
    lt_of_le_of_lt ((card_le_univ _).trans (by simp)) hB
  let e : (Σ j : Fin (d + 1), Σ v : Fin B, Fin (typeVec (ps j) v.val)) ≃
      (Σ j : Fin (d + 1), Fin (ps j).length) :=
    Equiv.sigmaCongrRight (fun j => typeEquiv B (hcard j) (ps j))
  have hs : ((fun b : (Σ j : Fin (d + 1), Fin (ps j).length) => (ps b.1).partSize b.2) ∘ e) =
      (fun b : (Σ j : Fin (d + 1), Σ v : Fin B, Fin (typeVec (ps j) v.val)) => b.2.1.val) := by
    funext ⟨j, v, t⟩
    exact typeEquiv_size B (hcard j) (ps j) v t
  have hc : ((fun b : (Σ j : Fin (d + 1), Fin (ps j).length) => b.1) ∘ e) =
      (fun b : (Σ j : Fin (d + 1), Σ v : Fin B, Fin (typeVec (ps j) v.val)) => b.1) := by
    funext ⟨j, v, t⟩
    rfl
  have h := card_blkAdm_equiv e (fun b : (Σ j : Fin (d + 1), Fin (ps j).length) => (ps b.1).partSize b.2)
    (fun b => b.1) (fun i => (S i).card) (fixedPathQuality S) rho i
  rw [hs, hc] at h
  rw [cntU, Fintype.card_subtype]
  exact (card_filter_inst _).trans (h.trans (card_filter_inst _))

end GradientKey.Concrete
