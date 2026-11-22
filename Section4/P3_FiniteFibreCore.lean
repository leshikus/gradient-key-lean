import Mathlib

/-!
# Generic finite-uniform fibre disintegration (P3 reusable core)

This file is independent of `GradientKeySection4.lean`. It proves exact
finite fibre summation and the positive-fibre mean and tail transfers.
Status: NOT COMPILED in this environment.
-/

noncomputable section

namespace GradientKey.P3

open Finset

/-! ## Generic finite disintegration, including empty fibres -/

/-- A publicly accessible finite-uniform mean. The P0 baseline currently
    declares the identically defined `GradientKey.finiteAverage` private. -/
def uniformMean {α : Type*} [Fintype α] [Nonempty α]
    (u : α → ℝ) : ℝ :=
  (∑ a : α, u a) / (Fintype.card α : ℝ)

namespace FiniteFibre

variable {α β : Type*} [Fintype α] [Fintype β]

/-- One fibre, possibly empty. -/
abbrev Fibre (q : α → β) (b : β) := {a : α // q a = b}

noncomputable instance fibreFintype (q : α → β) (b : β) :
    Fintype (Fibre q b) := by
  classical
  infer_instance

/-- The canonical equivalence between points and their labelled fibres. -/
def sigmaEquiv (q : α → β) :
    α ≃ (Σ b : β, Fibre q b) where
  toFun a := ⟨q a, ⟨a, rfl⟩⟩
  invFun t := t.2.1
  left_inv := by
    intro a
    rfl
  right_inv := by
    rintro ⟨b, ⟨a, ha⟩⟩
    cases ha
    rfl

/-- Exact fibre summation, including zero-cardinality fibres. -/
theorem sum_over_fibres (q : α → β) (u : α → ℝ) :
    (∑ a : α, u a) =
      ∑ b : β, ∑ a : Fibre q b, u a.1 := by
  classical
  calc
    (∑ a : α, u a) =
        ∑ t : (Σ b : β, Fibre q b), u t.2.1 := by
          exact (Equiv.sum_comp (sigmaEquiv q).symm u).symm
    _ = ∑ b : β, ∑ a : Fibre q b, u a.1 := by
          rw [Fintype.sum_sigma]

/-- Cardinality is the sum of the cardinalities of all fibres. -/
theorem card_over_fibres (q : α → β) :
    (Fintype.card α : ℝ) =
      ∑ b : β, (Fintype.card (Fibre q b) : ℝ) := by
  classical
  simpa using (sum_over_fibres q (fun _ => (1 : ℝ)))

/-- Exact finite tower identity, with the globally normalized mean. -/
theorem tower_sum [Nonempty α] (q : α → β) (u : α → ℝ) :
    uniformMean u =
      (∑ b : β, ∑ a : Fibre q b, u a.1) /
        (Fintype.card α : ℝ) := by
  rw [uniformMean, sum_over_fibres q u]

/-- Transfer any fibrewise sum bound. No independence assumptions. -/
theorem bound_from_fibre_sums [Nonempty α]
    (q : α → β) (u : α → ℝ) (c : ℝ)
    (h : ∀ b : β,
      (∑ a : Fibre q b, u a.1) ≤
        (Fintype.card (Fibre q b) : ℝ) * c) :
    uniformMean u ≤ c := by
  classical
  have hN : (∑ a : α, u a) ≤ (Fintype.card α : ℝ) * c := by
    calc
      (∑ a : α, u a) =
          ∑ b : β, ∑ a : Fibre q b, u a.1 := sum_over_fibres q u
      _ ≤ ∑ b : β, (Fintype.card (Fibre q b) : ℝ) * c := by
            apply Finset.sum_le_sum
            intro b _
            exact h b
      _ = (Fintype.card α : ℝ) * c := by
            rw [← Finset.sum_mul, ← card_over_fibres q]
  have hpos : (0 : ℝ) < Fintype.card α := by
    exact_mod_cast (Fintype.card_pos : 0 < Fintype.card α)
  exact (div_le_iff₀ hpos).2 (by rw [mul_comm]; exact hN)

/-- Conditional expectation bounds only have to be specified for
    positive-cardinality fibres. All empty fibres contribute zero. -/
theorem bound_from_positive_fibre_means [Nonempty α]
    (q : α → β) (u : α → ℝ) (c : ℝ)
    (h : ∀ b : β, 0 < Fintype.card (Fibre q b) →
      (∑ a : Fibre q b, u a.1) /
        (Fintype.card (Fibre q b) : ℝ) ≤ c) :
    uniformMean u ≤ c := by
  classical
  apply bound_from_fibre_sums q u c
  intro b
  by_cases hb : 0 < Fintype.card (Fibre q b)
  · have hbR : (0 : ℝ) < Fintype.card (Fibre q b) := by
      exact_mod_cast hb
    rw [mul_comm]
    exact (div_le_iff₀ hbR).1 (h b hb)
  · have hb0 : Fintype.card (Fibre q b) = 0 := Nat.eq_zero_of_not_pos hb
    letI : IsEmpty (Fibre q b) := (Fintype.card_eq_zero_iff).1 hb0
    simp

/-- Transfer conditional tail-probability bounds. Applying the preceding
    mean bound to an indicator is a finite law of total probability. -/
theorem tail_from_positive_fibre_tails [Nonempty α]
    (q : α → β) (u : α → ℝ) (z c : ℝ)
    (h : ∀ b : β, 0 < Fintype.card (Fibre q b) →
      (∑ a : Fibre q b, if z < u a.1 then (1 : ℝ) else 0) /
        (Fintype.card (Fibre q b) : ℝ) ≤ c) :
    uniformMean (fun a => if z < u a then (1 : ℝ) else 0) ≤ c := by
  exact bound_from_positive_fibre_means q
    (fun a => if z < u a then (1 : ℝ) else 0) c h

end FiniteFibre

end GradientKey.P3
