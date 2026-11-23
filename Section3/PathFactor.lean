import Counting
import Mobius

/-!
# Proposition 3.2: row independence and Möbius inversion

The two lemmas in this file are generic. They do not postulate any
assumptions about the greedy algorithm. The path formula will use them
with the row predicate derived from its greedy-path characterization.

Draft against Lean v4.36.0 and pinned Mathlib v4.36.0.
-/

noncomputable section

namespace GradientKey.Concrete

open Finset Classical

variable {n m : ℕ}

/-- A system of independent row predicates on a binary table is equivalent
    to choosing one admissible row at each index. -/
def rowConstraintEquiv
    (P : Fin n → (Fin m → Bool) → Prop) :
    {A : Table n m // ∀ i, P i (A i)} ≃
      ((i : Fin n) → {r : Fin m → Bool // P i r}) where
  toFun A i := ⟨A.1 i, A.2 i⟩
  invFun rows := ⟨fun i => (rows i).1, fun i => (rows i).2⟩
  left_inv A := by
    apply Subtype.ext
    rfl
  right_inv rows := by
    funext i
    apply Subtype.ext
    rfl

/-- The exact finite cardinality factorization used in the path formula. -/
theorem card_row_constraints
    (P : Fin n → (Fin m → Bool) → Prop) :
    Fintype.card {A : Table n m // ∀ i, P i (A i)} =
      ∏ i : Fin n, Fintype.card {r : Fin m → Bool // P i r} := by
  classical
  calc
    _ = Fintype.card ((i : Fin n) → {r : Fin m → Bool // P i r}) :=
      Fintype.card_congr (rowConstraintEquiv P)
    _ = _ := Fintype.card_pi

/-- The same factorization stated with `Finset` counts. -/
theorem card_row_constraints_filter
    (P : Fin n → (Fin m → Bool) → Prop) :
    (univ.filter (fun A : Table n m => ∀ i, P i (A i))).card =
      ∏ i : Fin n,
        (univ.filter (fun r : Fin m → Bool => P i r)).card := by
  classical
  rw [← Fintype.card_subtype, card_row_constraints]
  apply Finset.prod_congr rfl
  intro i _
  rw [Fintype.card_subtype]

/-- Equality of full column-vectors on partition blocks is equivalent
    to block-constancy in each separate row. -/
theorem constOn_columns_iff_rows
    (c : OrderedFinpartition m) (A : Table n m) :
    ConstOn c (fun j : Fin m => fun i : Fin n => A i j) ↔
      ∀ i : Fin n, ConstOn c (A i) := by
  unfold ConstOn
  constructor
  · intro h i b u v
    exact congrFun (h b u v) i
  · intro h b u v
    funext i
    exact h i b u v

/-- Möbius inversion applied to the existing `Table`/`DistinctColumns`.
    This is precisely the column-injectivity correction needed before
    factoring the unrestricted table count over its rows. -/
theorem mobius_table_indicator (A : Table n m) :
    (∑ c : OrderedFinpartition m,
      if (∀ i : Fin n, ConstOn c (A i)) then mu c else 0) =
      if DistinctColumns A then 1 else 0 := by
  classical
  calc
    _ = ∑ c : OrderedFinpartition m,
          if ConstOn c (fun j : Fin m => fun i : Fin n => A i j) then mu c else 0 := by
        apply Finset.sum_congr rfl
        intro c _
        exact if_congr (constOn_columns_iff_rows c A).symm rfl rfl
    _ = _ := by
        rw [mobius_injective m (fun j : Fin m => fun i : Fin n => A i j)]
        exact if_congr Iff.rfl rfl rfl

/-- A partition-respecting row predicate remains independent across rows. -/
theorem card_row_constraints_constOn
    (P : Fin n → (Fin m → Bool) → Prop)
    (c : OrderedFinpartition m) :
    (univ.filter (fun A : Table n m =>
      ∀ i, P i (A i) ∧ ConstOn c (A i))).card =
      ∏ i : Fin n,
        (univ.filter (fun r : Fin m → Bool =>
          P i r ∧ ConstOn c r)).card :=
  by convert card_row_constraints_filter (fun i r => P i r ∧ ConstOn c r)

end GradientKey.Concrete
