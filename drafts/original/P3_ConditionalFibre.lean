import GradientKeySection4
import P3_FiniteFibreCore

/-!
# P3: finite row-deletion disintegration

Companion to `GradientKeySection4.lean` (the paper's Section 4).

No change to the greedy algorithm, its first-in-row-order tie breaking,
or its treatment of repeated columns in a row-deleted table is made here.
We use `Fin.removeNth` / `Fin.insertNth` to preserve row order.

This source has NOT BEEN COMPILED in the present environment. The exact
Mathlib/Lean versions must be inherited from the P0 project. There are
no new axioms and no admitted proof terms. The last theorem below is
an explicit interface for the tail bound to be supplied by the Hoeffding
agent; it does NOT purport to prove that tail bound.
-/

noncomputable section

namespace GradientKey.P3

open Finset GradientKey.Concrete GradientKey.RowDeletion

/-! ## Deletion and reinsertion at the *original* row position -/

variable {n m : ℕ}

/-- Public finite enumeration of the baseline's subtype of distinct-column
    tables, needed for the row-deletion fibres. -/
noncomputable instance validTableFintype (n m : ℕ) :
    Fintype (Concrete.ValidTable n m) := by
  classical
  infer_instance

/-- Delete row `r`, preserving the order of all other rows. -/
def deleteRow (A : Concrete.Table (n + 1) m) (r : Fin (n + 1)) :
    RowDeletion.RemainingTable n m :=
  r.removeNth A

/-- Restore the missing row at position `r`, preserving all others. -/
def insertRow (B : RowDeletion.RemainingTable n m)
    (r : Fin (n + 1)) (x : Fin m → Bool) :
    Concrete.Table (n + 1) m :=
  r.insertNth x B

@[simp] theorem deleteRow_insertRow (B : RowDeletion.RemainingTable n m)
    (r : Fin (n + 1)) (x : Fin m → Bool) :
    deleteRow (insertRow B r x) r = B := by
  exact Fin.removeNth_insertNth r x B

@[simp] theorem insertRow_deleteRow (A : Concrete.Table (n + 1) m)
    (r : Fin (n + 1)) :
    insertRow (deleteRow A r) r (A r) = A := by
  exact Fin.insertNth_self_removeNth r A

@[simp] theorem insertRow_at (B : RowDeletion.RemainingTable n m)
    (r : Fin (n + 1)) (x : Fin m → Bool) :
    insertRow B r x r = x := by
  exact Fin.insertNth_apply_same r x B

@[simp] theorem insertRow_other (B : RowDeletion.RemainingTable n m)
    (r : Fin (n + 1)) (x : Fin m → Bool) (k : Fin n) :
    insertRow B r x (r.succAbove k) = B k := by
  exact Fin.insertNth_apply_succAbove r x B k

/-- The baseline's `DistinctColumns` is equivalent to the baseline's
    `ValidExtension`; this is the structural heart of the bijection. -/
theorem distinct_insertRow_iff (B : RowDeletion.RemainingTable n m)
    (r : Fin (n + 1)) (x : Fin m → Bool) :
    Concrete.DistinctColumns (insertRow B r x) ↔
      RowDeletion.ValidExtension B x := by
  constructor
  · intro hDist a b hab hB
    intro hx
    apply hab
    apply hDist
    funext k
    rcases Fin.eq_self_or_eq_succAbove r k with hk | ⟨i, hi⟩
    · subst k
      simpa only [insertRow_at] using hx
    · subst k
      simpa only [insertRow_other] using hB i
  · intro hx a b heq
    by_contra hab
    have hSame : RowDeletion.SameColumn B a b := by
      intro k
      have hk := congrFun heq (r.succAbove k)
      simpa only [insertRow_other] using hk
    have hRow : x a = x b := by
      have hr := congrFun heq r
      simpa only [insertRow_at] using hr
    exact (hx a b hab hSame) hRow

/-! ## The table and table-column fibres -/

/-- All valid full tables whose deletion at `r` is exactly `B`. -/
abbrev TableFibre (B : RowDeletion.RemainingTable n m)
    (r : Fin (n + 1)) :=
  {A : Concrete.ValidTable (n + 1) m // deleteRow A.1 r = B}

noncomputable instance tableFibreFintype
    (B : RowDeletion.RemainingTable n m) (r : Fin (n + 1)) :
    Fintype (TableFibre B r) := by
  classical
  infer_instance

/-- A table in a fixed fibre is determined by its inserted row. -/
def tableFibreEquiv (B : RowDeletion.RemainingTable n m)
    (r : Fin (n + 1)) : TableFibre B r ≃ RowDeletion.Extension B where
  toFun A := by
    let x := A.1.1 r
    have hA : insertRow B r x = A.1.1 := by
      change insertRow B r (A.1.1 r) = A.1.1
      rw [← A.2]
      exact insertRow_deleteRow A.1.1 r
    refine ⟨x, (distinct_insertRow_iff B r x).1 ?_⟩
    rw [hA]
    exact A.1.2
  invFun x :=
    ⟨⟨insertRow B r x.1, (distinct_insertRow_iff B r x.1).2 x.2⟩,
      deleteRow_insertRow B r x.1⟩
  left_inv := by
    intro A
    apply Subtype.ext
    apply Subtype.ext
    change insertRow B r (A.1.1 r) = A.1.1
    rw [← A.2]
    exact insertRow_deleteRow A.1.1 r
  right_inv := by
    intro x
    apply Subtype.ext
    exact insertRow_at B r x.1

/-- No feasibility is assumed: the fibre is inhabited iff a valid
    inserted row exists. In particular, repeated columns in `B` are allowed. -/
theorem table_fibre_feasible_iff (B : RowDeletion.RemainingTable n m)
    (r : Fin (n + 1)) :
    (∃ A : Concrete.ValidTable (n + 1) m, deleteRow A.1 r = B) ↔
      Nonempty (RowDeletion.Extension B) := by
  constructor
  · rintro ⟨A, hA⟩
    exact ⟨tableFibreEquiv B r ⟨A, hA⟩⟩
  · rintro ⟨x⟩
    exact ⟨((tableFibreEquiv B r).symm x).1,
      ((tableFibreEquiv B r).symm x).2⟩

/-- Fibre cardinality, without a nonemptiness hypothesis. -/
theorem table_fibre_card (B : RowDeletion.RemainingTable n m)
    (r : Fin (n + 1)) :
    Fintype.card (TableFibre B r) =
      Fintype.card (RowDeletion.Extension B) := by
  classical
  exact Fintype.card_congr (tableFibreEquiv B r)

/-- The sampled key fixes both the remaining table and independently
    chosen column. The sample type is a CARTESIAN PRODUCT. -/
def sampleKey (r : Fin (n + 1))
    (ω : Concrete.Sample (n + 1) m) :
    RowDeletion.RemainingTable n m × Fin m :=
  (deleteRow ω.1.1 r, ω.2)

abbrev SampleFibre (B : RowDeletion.RemainingTable n m)
    (r : Fin (n + 1)) (j₀ : Fin m) :=
  FiniteFibre.Fibre (sampleKey r) (B, j₀)

/-- A joint fibre `deleteRow A r = B ∧ j = j₀` contains exactly one
    sampled pair for each admissible inserted row. -/
def sampleFibreEquiv (B : RowDeletion.RemainingTable n m)
    (r : Fin (n + 1)) (j₀ : Fin m) :
    SampleFibre B r j₀ ≃ RowDeletion.Extension B where
  toFun ω := by
    have hB : deleteRow ω.1.1.1 r = B :=
      congrArg Prod.fst ω.2
    let A : TableFibre B r := ⟨ω.1.1, hB⟩
    exact tableFibreEquiv B r A
  invFun x := by
    let A : TableFibre B r := (tableFibreEquiv B r).symm x
    refine ⟨(A.1, j₀), ?_⟩
    change (deleteRow A.1.1 r, j₀) = (B, j₀)
    rw [A.2]
  left_inv := by
    intro ω
    apply Subtype.ext
    apply Prod.ext
    · apply Subtype.ext
      change insertRow B r (ω.1.1.1 r) = ω.1.1.1
      have hB : deleteRow ω.1.1.1 r = B := congrArg Prod.fst ω.2
      rw [← hB]
      exact insertRow_deleteRow ω.1.1.1 r
    · exact (congrArg Prod.snd ω.2).symm
  right_inv := by
    intro x
    apply Subtype.ext
    change insertRow B r x.1 r = x.1
    exact insertRow_at B r x.1

/-- The independent column choice contributes one factor of `m` to
    the full sample space. -/
theorem sample_card_factor (n m : ℕ) :
    Fintype.card (Concrete.Sample n m) =
      Fintype.card (Concrete.ValidTable n m) * m := by
  classical
  simp [Concrete.Sample, Fintype.card_prod]

/-- In particular a joint conditioning fibre has exactly as many
    outcomes as `Extension B`; no spurious factor of `m` survives. -/
theorem sample_fibre_card (B : RowDeletion.RemainingTable n m)
    (r : Fin (n + 1)) (j₀ : Fin m) :
    Fintype.card (SampleFibre B r j₀) =
      Fintype.card (RowDeletion.Extension B) := by
  classical
  exact Fintype.card_congr (sampleFibreEquiv B r j₀)

/-- Exact conditional law, for ANY test function. The positivity guard
    excludes conditioning on a probability-zero event. -/
theorem conditional_sample_mean_eq_extension
    (B : RowDeletion.RemainingTable n m) (r : Fin (n + 1))
    (j₀ : Fin m)
    (hpos : 0 < Fintype.card (SampleFibre B r j₀))
    (u : (Fin m → Bool) → ℝ) :
    (∑ ω : SampleFibre B r j₀, u (ω.1.1.1 r)) /
        (Fintype.card (SampleFibre B r j₀) : ℝ) =
    (∑ x : RowDeletion.Extension B, u x.1) /
        (Fintype.card (RowDeletion.Extension B) : ℝ) := by
  classical
  have hsum :
      (∑ ω : SampleFibre B r j₀, u (ω.1.1.1 r)) =
        ∑ x : RowDeletion.Extension B, u x.1 := by
    calc
      (∑ ω : SampleFibre B r j₀, u (ω.1.1.1 r)) =
          ∑ x : RowDeletion.Extension B,
            u (((sampleFibreEquiv B r j₀).symm x).1.1.1 r) := by
              exact (Equiv.sum_comp (sampleFibreEquiv B r j₀).symm
                (fun ω : SampleFibre B r j₀ => u (ω.1.1.1 r))).symm
      _ = ∑ x : RowDeletion.Extension B, u x.1 := by
            apply Finset.sum_congr rfl
            intro x _
            simp [sampleFibreEquiv, tableFibreEquiv, insertRow_at]
  rw [hsum, sample_fibre_card]

/-- Explicit equal point masses: the inserted row is conditionally uniform. -/
theorem conditional_inserted_row_uniform
    (B : RowDeletion.RemainingTable n m) (r : Fin (n + 1))
    (j₀ : Fin m)
    (hpos : 0 < Fintype.card (SampleFibre B r j₀))
    (x : RowDeletion.Extension B) :
    (∑ ω : SampleFibre B r j₀,
       if ω.1.1.1 r = x.1 then (1 : ℝ) else 0) /
        (Fintype.card (SampleFibre B r j₀) : ℝ) =
      1 / (Fintype.card (RowDeletion.Extension B) : ℝ) := by
  rw [conditional_sample_mean_eq_extension B r j₀ hpos
    (fun y => if y = x.1 then (1 : ℝ) else 0)]
  have hsum :
      (∑ y : RowDeletion.Extension B,
        if y.1 = x.1 then (1 : ℝ) else 0) = 1 := by
    simp [Subtype.ext_iff]
  rw [hsum]

/-- Exact conditional imbalance in the paper's notation. This composes
    the new probabilistic bijection with the baseline's already established
    `conditional_inserted_imbalance_exact` theorem. -/
theorem conditional_sample_imbalance_exact
    (B : RowDeletion.RemainingTable n m) (r : Fin (n + 1))
    (j₀ : Fin m) (hpos : 0 < Fintype.card (SampleFibre B r j₀))
    (S : Finset (Fin m)) (hclosed : RowDeletion.PairClosed B S) :
    (∑ ω : SampleFibre B r j₀,
        RowDeletion.insertedImbalance (ω.1.1.1 r) S) /
          (Fintype.card (SampleFibre B r j₀) : ℝ) =
      ((RowDeletion.uniqueIn B S).card : ℝ) / (S.card : ℝ) := by
  have hposE : 0 < Fintype.card (RowDeletion.Extension B) := by
    simpa only [sample_fibre_card B r j₀] using hpos
  letI : Nonempty (RowDeletion.Extension B) :=
    Fintype.card_pos_iff.mp hposE
  have hExact := RowDeletion.conditional_inserted_imbalance_exact B S hclosed
  change (∑ x : RowDeletion.Extension B,
      RowDeletion.insertedImbalance x.1 S) /
      (Fintype.card (RowDeletion.Extension B) : ℝ) =
      ((RowDeletion.uniqueIn B S).card : ℝ) / (S.card : ℝ) at hExact
  exact (conditional_sample_mean_eq_extension B r j₀ hpos
    (fun x => RowDeletion.insertedImbalance x S)).trans hExact

/-! ## No-independence tower for row-deleted candidate sets -/

/-- A row-deleted candidate set is a function of the row-deleted table
    and the independently selected column, NOT of the inserted row. -/
def sampleU (r : Fin (n + 1))
    (candidate : RowDeletion.RemainingTable n m → Fin m → Finset (Fin m))
    (ω : Concrete.Sample (n + 1) m) : ℝ :=
  RowDeletion.insertedImbalance (ω.1.1 r)
    (candidate (deleteRow ω.1.1 r) ω.2)

/-- Unconditional `E[U_r] ≤ 1`, with geometric conditions required only
    for feasible fibres. This does not posit independence of `candidate`
    and the missing row; it proves the relevant conditional uniformity. -/
theorem unconditional_row_mean_le_one
    [Nonempty (Concrete.Sample (n + 1) m)]
    (r : Fin (n + 1))
    (candidate : RowDeletion.RemainingTable n m → Fin m → Finset (Fin m))
    (hCandidates : ∀ (B : RowDeletion.RemainingTable n m) (j₀ : Fin m),
      0 < Fintype.card (SampleFibre B r j₀) →
      0 < (candidate B j₀).card ∧
        RowDeletion.PairClosed B (candidate B j₀)) :
    uniformMean (sampleU r candidate) ≤ 1 := by
  classical
  apply FiniteFibre.bound_from_positive_fibre_means
    (q := sampleKey r) (u := sampleU r candidate) (c := 1)
  rintro ⟨B, j₀⟩ hpos
  have hposE : 0 < Fintype.card (RowDeletion.Extension B) := by
    simpa only [sample_fibre_card B r j₀] using hpos
  letI : Nonempty (RowDeletion.Extension B) :=
    Fintype.card_pos_iff.mp hposE
  obtain ⟨hS, hClosed⟩ := hCandidates B j₀ hpos
  have hOne := RowDeletion.conditional_inserted_imbalance_le_one
    B (candidate B j₀) hS hClosed
  change (∑ x : RowDeletion.Extension B,
      RowDeletion.insertedImbalance x.1 (candidate B j₀)) /
      (Fintype.card (RowDeletion.Extension B) : ℝ) ≤ 1 at hOne
  have hrewrite :
      (∑ ω : SampleFibre B r j₀, sampleU r candidate ω.1) =
      (∑ ω : SampleFibre B r j₀,
        RowDeletion.insertedImbalance (ω.1.1.1 r) (candidate B j₀)) := by
    apply Finset.sum_congr rfl
    intro ω _
    have hk : sampleKey r ω.1 = (B, j₀) := ω.2
    have hB : deleteRow ω.1.1.1 r = B := congrArg Prod.fst hk
    have hj : ω.1.2 = j₀ := congrArg Prod.snd hk
    simp only [sampleU]
    rw [hB, hj]
  rw [hrewrite]
  exact (conditional_sample_mean_eq_extension B r j₀ hpos
    (fun x => RowDeletion.insertedImbalance x (candidate B j₀))).le.trans hOne

/-- Tail transfer. The *only* external obligation is the Hoeffding
    bound on each fixed nonempty extension fibre, which belongs to the
    separate tail agent. No spurious independence of candidate sets is used. -/
theorem unconditional_row_tail_of_extension_tails
    [Nonempty (Concrete.Sample (n + 1) m)]
    (r : Fin (n + 1))
    (candidate : RowDeletion.RemainingTable n m → Fin m → Finset (Fin m))
    (z c : ℝ)
    (hTail : ∀ (B : RowDeletion.RemainingTable n m) (j₀ : Fin m),
      0 < Fintype.card (RowDeletion.Extension B) →
      (∑ x : RowDeletion.Extension B,
        if z < RowDeletion.insertedImbalance x.1 (candidate B j₀)
        then (1 : ℝ) else 0) /
          (Fintype.card (RowDeletion.Extension B) : ℝ) ≤ c) :
    uniformMean (fun ω : Concrete.Sample (n + 1) m =>
        if z < sampleU r candidate ω then (1 : ℝ) else 0) ≤ c := by
  classical
  apply FiniteFibre.tail_from_positive_fibre_tails
    (q := sampleKey r) (u := sampleU r candidate) (z := z) (c := c)
  rintro ⟨B, j₀⟩ hpos
  have hposE : 0 < Fintype.card (RowDeletion.Extension B) := by
    simpa only [sample_fibre_card B r j₀] using hpos
  have hrewrite :
      (∑ ω : SampleFibre B r j₀,
        if z < sampleU r candidate ω.1 then (1 : ℝ) else 0) =
      (∑ ω : SampleFibre B r j₀,
        if z < RowDeletion.insertedImbalance (ω.1.1.1 r) (candidate B j₀)
        then (1 : ℝ) else 0) := by
    apply Finset.sum_congr rfl
    intro ω _
    have hk : sampleKey r ω.1 = (B, j₀) := ω.2
    have hB : deleteRow ω.1.1.1 r = B := congrArg Prod.fst hk
    have hj : ω.1.2 = j₀ := congrArg Prod.snd hk
    simp only [sampleU]
    rw [hB, hj]
  rw [hrewrite]
  have hEq := conditional_sample_mean_eq_extension B r j₀ hpos
    (fun x => if z < RowDeletion.insertedImbalance x (candidate B j₀)
      then (1 : ℝ) else 0)
  exact hEq.le.trans (hTail B j₀ hposE)

end GradientKey.P3
