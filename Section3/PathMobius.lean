import PathFactor

/-!
# Proposition 3.2: generic Möbius-corrected row product

This is the main algebraic reduction in Steps 4--5 of the article's proof.
It does not use any special property of the greedy algorithm: `P i row`
is an *arbitrary* condition on an individual row.

The LHS counts tables with pairwise distinct columns satisfying every
row condition. The RHS applies existing partition Möbius coefficients
and factors the count into the independent rows.

-/

noncomputable section

namespace GradientKey.Concrete

open Finset Classical

variable {n m : ℕ}

/-- Generic rowwise version of Möbius inversion:

  #{A : Table n m | columns injective, forall i, P i (A i)}
    = sum_pi mu(pi) * prod_i #{row | P i row and ConstOn pi row}.

The sum is in `ℤ` because the Möbius coefficients may be negative.
-/
theorem card_valid_with_row_constraints
    (P : Fin n → (Fin m → Bool) → Prop) :
    (∑ A : Table n m,
      if (∀ i : Fin n, P i (A i)) ∧ DistinctColumns A then (1 : ℤ) else 0) =
    ∑ c : OrderedFinpartition m,
      mu c * ∏ i : Fin n,
        ((univ.filter (fun row : Fin m → Bool =>
          P i row ∧ ConstOn c row)).card : ℤ) := by
  classical
  have hpoint (A : Table n m) :
      (if (∀ i : Fin n, P i (A i)) ∧ DistinctColumns A then (1 : ℤ) else 0) =
      ∑ c : OrderedFinpartition m,
        if (∀ i : Fin n, P i (A i) ∧ ConstOn c (A i)) then mu c else 0 := by
    by_cases hp : ∀ i : Fin n, P i (A i)
    · have hc : ∀ c : OrderedFinpartition m,
          (∀ i : Fin n, P i (A i) ∧ ConstOn c (A i)) ↔
          (∀ i : Fin n, ConstOn c (A i)) := by
        intro c
        constructor
        · intro h i; exact (h i).2
        · intro h i; exact ⟨hp i, h i⟩
      rw [if_congr (show ((∀ i : Fin n, P i (A i)) ∧ DistinctColumns A) ↔ DistinctColumns A from
        ⟨fun h => h.2, fun h => ⟨hp, h⟩⟩) rfl rfl, ← mobius_table_indicator A]
      apply Finset.sum_congr rfl
      intro c _
      exact if_congr (hc c).symm rfl rfl
    · have he : ¬∃ c : OrderedFinpartition m,
          ∀ i : Fin n, P i (A i) ∧ ConstOn c (A i) := by
        rintro ⟨c, hc⟩
        apply hp
        intro i
        exact (hc i).1
      have hfalse (c : OrderedFinpartition m) :
          ¬ (∀ i : Fin n, P i (A i) ∧ ConstOn c (A i)) :=
        fun hc => he ⟨c, hc⟩
      simp [hp, hfalse]
  calc
    _ = ∑ A : Table n m,
          ∑ c : OrderedFinpartition m,
            if (∀ i : Fin n, P i (A i) ∧ ConstOn c (A i)) then mu c else 0 := by
          apply Finset.sum_congr rfl
          intro A _
          exact hpoint A
    _ = ∑ c : OrderedFinpartition m,
          ∑ A : Table n m,
            if (∀ i : Fin n, P i (A i) ∧ ConstOn c (A i)) then mu c else 0 := by
          rw [Finset.sum_comm]
    _ = ∑ c : OrderedFinpartition m,
          mu c * ∏ i : Fin n,
            ((univ.filter (fun row : Fin m → Bool =>
              P i row ∧ ConstOn c row)).card : ℤ) := by
          apply Finset.sum_congr rfl
          intro c _
          have hcount :
              (∑ A : Table n m,
                if (∀ i : Fin n, P i (A i) ∧ ConstOn c (A i)) then mu c else 0) =
              ((univ.filter (fun A : Table n m =>
                ∀ i, P i (A i) ∧ ConstOn c (A i))).card : ℤ) * mu c := by
            rw [← Finset.sum_filter]
            simp [mul_comm]
          rw [hcount, card_row_constraints_constOn P c]
          push_cast
          ring

end GradientKey.Concrete
