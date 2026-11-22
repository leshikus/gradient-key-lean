import Mathlib

/-!
# P2: the finite candidate-size transition (Section 4, Lemma 4.1)

This module deliberately does NOT depend on the uncompiled v4 baseline.
Its central finite statement works for *every* partition of a finite
column set into fibres of a key and for *every* Boolean splitting map.
In particular it does not require random or independent splits.

Integration into `GradientKey.Concrete` requires the separately stated
candidate/fibre compatibility lemmas.  No logical claim about the concrete
sample is made without those lemmas.

STATUS: NOT COMPILED (Lean, Lake, Mathlib unavailable in the runtime).
-/

noncomputable section

namespace GradientKey.P2

open Finset

variable {J C : Type*} [Fintype J] [Fintype C] [DecidableEq C]

/-- Columns with a given candidate-set identifier. -/
def fiber (key : J → C) (c : C) : Finset J :=
  Finset.univ.filter (fun j => key j = c)

/-- Count of columns with this identifier. -/
def parentCount (key : J → C) (c : C) : ℕ := (fiber key c).card

/-- Child sizes for the two possible results of the chosen test. -/
def trueCount (key : J → C) (bit : J → Bool) (c : C) : ℕ :=
  ((fiber key c).filter (fun j => bit j = true)).card

def falseCount (key : J → C) (bit : J → Bool) (c : C) : ℕ :=
  ((fiber key c).filter (fun j => bit j = false)).card

private theorem bool_filter_cards (S : Finset J) (bit : J → Bool) :
    (S.filter (fun j => bit j = true)).card +
      (S.filter (fun j => bit j = false)).card = S.card := by
  classical
  have h := Finset.card_filter_add_card_filter_not
    (s := S) (fun j => bit j = true)
  simpa using h

theorem trueCount_add_falseCount (key : J → C) (bit : J → Bool)
    (c : C) :
    trueCount key bit c + falseCount key bit c = parentCount key c :=
  bool_filter_cards (fiber key c) bit

/-- This is a finite counting equality, NOT an assertion of conditional
uniformity: each column occurs once, in exactly one fibre. -/
theorem sum_by_fiber (key : J → C) (f : C → ℝ) :
    (∑ j : J, f (key j)) =
      ∑ c : C, (parentCount key c : ℝ) * f c := by
  classical
  calc
    (∑ j : J, f (key j)) =
        ∑ j : J, ∑ c : C, if key j = c then f c else 0 := by
          apply Finset.sum_congr rfl
          intro j hj
          simp
    _ = ∑ c : C, ∑ j : J, if key j = c then f c else 0 := by
          rw [Finset.sum_comm]
    _ = ∑ c : C, (parentCount key c : ℝ) * f c := by
          apply Finset.sum_congr rfl
          intro c hc
          simp [parentCount, fiber, Finset.sum_ite, nsmul_eq_mul]

/-- The child that contains column `j` is precisely the fibre of the
(parent identifier, tested bit) pair. -/
def childCount (key : J → C) (bit : J → Bool) (j : J) : ℕ :=
  (fiber (fun k => (key k, bit k)) (key j, bit j)).card

private theorem pair_fiber_true (key : J → C) (bit : J → Bool) (c : C) :
    fiber (fun j => (key j, bit j)) (c, true) =
      (fiber key c).filter (fun j => bit j = true) := by
  classical
  ext j
  simp [fiber, Finset.filter_filter, Prod.mk.injEq, and_comm, and_left_comm]

private theorem pair_fiber_false (key : J → C) (bit : J → Bool) (c : C) :
    fiber (fun j => (key j, bit j)) (c, false) =
      (fiber key c).filter (fun j => bit j = false) := by
  classical
  ext j
  simp [fiber, Finset.filter_filter, Prod.mk.injEq, and_comm, and_left_comm]

/-- Summing over the *actual columns*, the next size is size-biased.
The equality is obtained by counting ordered pairs of columns that have
the same (parent,bit) identifier. -/
theorem sum_childCount (key : J → C) (bit : J → Bool) :
    (∑ j : J, (childCount key bit j : ℝ)) =
      ∑ c : C,
        ((trueCount key bit c : ℝ) ^ 2 +
          (falseCount key bit c : ℝ) ^ 2) := by
  classical
  let pairKey : J → C × Bool := fun j => (key j, bit j)
  have h := sum_by_fiber pairKey
    (fun p : C × Bool => (parentCount pairKey p : ℝ))
  change (∑ j : J, (parentCount pairKey (pairKey j) : ℝ)) = _
  rw [h]
  rw [Fintype.sum_prod_type]
  apply Finset.sum_congr rfl
  intro c hc
  simp [parentCount, pairKey, Fintype.sum_bool,
    pair_fiber_true, pair_fiber_false, trueCount, falseCount, pow_two]

/-- A singleton has one selected child of size one, regardless of its bit. -/
theorem singleton_childCount (key : J → C) (bit : J → Bool)
    (j : J) (hj : parentCount key (key j) = 1) :
    childCount key bit j = 1 := by
  classical
  have hjsub : fiber (fun k => (key k, bit k)) (key j, bit j) ⊆
      fiber key (key j) := by
    intro k hk
    have hpair : (key k, bit k) = (key j, bit j) :=
      (Finset.mem_filter.mp hk).2
    have hkey : key k = key j := congrArg Prod.fst hpair
    exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, hkey⟩
  have hone : j ∈ fiber (fun k => (key k, bit k)) (key j, bit j) :=
    Finset.mem_filter.mpr ⟨Finset.mem_univ _, rfl⟩
  have hupper : childCount key bit j ≤ 1 := by
    calc
      childCount key bit j ≤ parentCount key (key j) :=
        Finset.card_le_card hjsub
      _ = 1 := hj
  have hlower : 1 ≤ childCount key bit j :=
    Finset.one_le_card.mpr ⟨j, hone⟩
  omega

/-- The article's split imbalance. It is zero at singleton candidate sets,
not the imbalance of the unused (constant) row. -/
def imbalance (key : J → C) (bit : J → Bool) (c : C) : ℝ :=
  if 2 ≤ parentCount key c then
    (((trueCount key bit c : ℝ) - (falseCount key bit c : ℝ)) ^ 2) /
      (parentCount key c : ℝ)
  else 0

def forkFlag (key : J → C) (c : C) : ℝ :=
  if 2 ≤ parentCount key c then 1 else 0

/-- Exact fixed-parent algebra, including the `-1` excess correction. -/
theorem fixed_parent_identity (a b : ℝ) (hs : 0 < a + b) :
    (a * a + b * b) / (a + b) - 1 =
      (((a + b) - 1) - 1 + (a - b) ^ 2 / (a + b)) / 2 := by
  have hn : a + b ≠ 0 := ne_of_gt hs
  field_simp [hn]
  ring

/-- After multiplication by the number of columns in a parent cell,
its entire contribution to the recurrence is an elementary identity.
Empty fibres have zero weight; singleton fibres have zero imbalance and
zero fork indicator. -/
private theorem one_fiber_identity (key : J → C) (bit : J → Bool)
    (c : C) :
    (trueCount key bit c : ℝ) ^ 2 + (falseCount key bit c : ℝ) ^ 2 -
        (parentCount key c : ℝ) =
      (parentCount key c : ℝ) *
        (((parentCount key c : ℝ) - 1) - forkFlag key c +
          imbalance key bit c) / 2 := by
  have hab := trueCount_add_falseCount key bit c
  unfold forkFlag imbalance
  generalize trueCount key bit c = a at *
  generalize falseCount key bit c = b at *
  generalize parentCount key c = s at *
  subst hab
  by_cases hf : 2 ≤ a + b
  · rw [if_pos hf, if_pos hf]
    have hne : ((a + b : ℕ) : ℝ) ≠ 0 := by
      exact_mod_cast (show a + b ≠ 0 by omega)
    push_cast at hne ⊢
    field_simp
    ring
  · rw [if_neg hf, if_neg hf]
    rcases (show (a = 0 ∧ b = 0) ∨ (a = 1 ∧ b = 0) ∨ (a = 0 ∧ b = 1) by omega)
      with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;> norm_num

/-- Finite, UNCONDITIONAL candidate-size recurrence for a one-step split
of any finite partition. No conditional probability assumption is used. -/
theorem finite_partition_recurrence (key : J → C) (bit : J → Bool) :
    (∑ j : J, ((childCount key bit j : ℝ) - 1)) =
      ((∑ j : J, ((parentCount key (key j) : ℝ) - 1)) -
        (∑ j : J, forkFlag key (key j)) +
        (∑ j : J, imbalance key bit (key j))) / 2 := by
  classical
  have htotal : (∑ c : C, (parentCount key c : ℝ)) =
      (Fintype.card J : ℝ) := by
    have h := sum_by_fiber key (fun _ => (1 : ℝ))
    simpa using h.symm
  have hchild :
      (∑ j : J, ((childCount key bit j : ℝ) - 1)) =
        ∑ c : C,
          (((trueCount key bit c : ℝ) ^ 2 +
            (falseCount key bit c : ℝ) ^ 2) -
            (parentCount key c : ℝ)) := by
    simp only [Finset.sum_sub_distrib]
    rw [sum_childCount, htotal]
    simp
  have hparent := sum_by_fiber key
    (fun c => (parentCount key c : ℝ) - 1)
  have hflag := sum_by_fiber key (forkFlag key)
  have himb := sum_by_fiber key (imbalance key bit)
  rw [hchild, hparent, hflag, himb]
  rw [← Finset.sum_sub_distrib, ← Finset.sum_add_distrib,
      Finset.sum_div]
  apply Finset.sum_congr rfl
  intro c hc
  rw [one_fiber_identity key bit c]
  ring


/-!
## Explicit double finite sum over tables and columns

`T` can be `Concrete.ValidTable n m`, `J` can be `Fin m`, and `key A`
is the candidate-set identifier for a fixed matrix `A` and depth `i`.
The summation below is over *all* ordered pairs `(A,j)`; no probabilistic
independence or conditional-law lemma is assumed.
-/

section Tables

variable {T : Type*} [Fintype T]

/-- The literal double finite average over tables and columns. -/
def pairAverage (f : T × J → ℝ) : ℝ :=
  (∑ A : T, ∑ j : J, f (A, j)) /
    (Fintype.card (T × J) : ℝ)

/-- A one-level path snapshot indexed by the table, with candidate
partition identifier and selected test's bit for every column. -/
structure FamilyStep (T J C : Type*) where
  key : T → J → C
  bit : T → J → Bool

namespace FamilyStep

variable (D : FamilyStep T J C)

/-- Number of candidates other than the selected column, before/after. -/
def excess (A : T) (j : J) : ℝ :=
  (parentCount (D.key A) ((D.key A) j) : ℝ) - 1

def nextExcess (A : T) (j : J) : ℝ :=
  (childCount (D.key A) (D.bit A) j : ℝ) - 1

def fork (A : T) (j : J) : ℝ :=
  forkFlag (D.key A) ((D.key A) j)

def splitImbalance (A : T) (j : J) : ℝ :=
  imbalance (D.key A) (D.bit A) ((D.key A) j)

/-- Finite sums over all matrices `A` and columns `j`. -/
theorem double_sum_recurrence :
    (∑ A : T, ∑ j : J, D.nextExcess A j) =
      ((∑ A : T, ∑ j : J, D.excess A j) -
        (∑ A : T, ∑ j : J, D.fork A j) +
        (∑ A : T, ∑ j : J, D.splitImbalance A j)) / 2 := by
  calc
    (∑ A : T, ∑ j : J, D.nextExcess A j) =
        ∑ A : T,
          ((∑ j : J, D.excess A j) -
            (∑ j : J, D.fork A j) +
            (∑ j : J, D.splitImbalance A j)) / 2 := by
              apply Finset.sum_congr rfl
              intro A hA
              exact finite_partition_recurrence (D.key A) (D.bit A)
    _ = _ := by
        rw [← Finset.sum_div, Finset.sum_add_distrib,
          Finset.sum_sub_distrib]

/-- The uniform `T × J` expectation has the paper's exact recurrence.
The concrete path is obtained only after proving that `D` describes
`Concrete.candidateAt` and the greedy selected row. -/
theorem pair_average_recurrence :
    pairAverage (fun w : T × J => D.nextExcess w.1 w.2) =
      (pairAverage (fun w : T × J => D.excess w.1 w.2) -
        pairAverage (fun w : T × J => D.fork w.1 w.2) +
        pairAverage (fun w : T × J => D.splitImbalance w.1 w.2)) / 2 := by
  unfold pairAverage
  rw [D.double_sum_recurrence]
  ring

end FamilyStep
end Tables

end GradientKey.P2
