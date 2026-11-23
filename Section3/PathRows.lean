import PathGreedy
import PathMobius
import RowList

/-!
# Proposition 3.2: rowwise admissibility for a fixed path

For fixed sets `S₀,...,S_d`, a distinguished column `j₀`, and an
injective schedule `ρ : Fin d ↪ Fin n`, the following predicates use only
one row at a time. The Möbius-corrected table count therefore factors.

The remaining geometric bridge is to show that the predicates precisely
characterize the *actual* greedy path when `S` is strictly nested and
all its candidate sets contain `j₀`. `PathGreedy` supplies the one-step
argmax equivalence needed for that bridge.

Draft, not compiled with the pinned Lean toolchain.
-/

noncomputable section

namespace GradientKey.Concrete

open Finset Classical

variable {n m d : ℕ}

/-- The quality of the specified split at depth `j`. -/
def fixedPathQuality
    (S : Fin (d + 1) → Finset (Fin m)) (j : Fin d) : ℕ :=
  min ((S (Fin.castSucc j) \ S (Fin.succ j)).card)
      (S (Fin.succ j)).card

/-- Local admissibility of a single row `row` at index `i`.
    At the selected index `i=ρ(j)`, the row makes exactly the chosen split.
    At every other index, its quality is strictly below the selected
    quality if it precedes the selected row, weakly below otherwise. -/
def fixedPathRowAdmissible
    (S : Fin (d + 1) → Finset (Fin m))
    (j₀ : Fin m) (rho : Fin d ↪ Fin n)
    (i : Fin n) (row : Row m) : Prop :=
  ∀ j : Fin d,
    (rho j = i →
      S (Fin.succ j) =
        (S (Fin.castSucc j)).filter (fun k => row k = row j₀)) ∧
    (rho j ≠ i →
      if i < rho j then
        rq (S (Fin.castSucc j)) row < fixedPathQuality S j
      else
        rq (S (Fin.castSucc j)) row ≤ fixedPathQuality S j)

/-- The joint predicate is a conjunction of independent row conditions. -/
def fixedPathRowwise
    (S : Fin (d + 1) → Finset (Fin m))
    (j₀ : Fin m) (rho : Fin d ↪ Fin n)
    (A : Table n m) : Prop :=
  ∀ i : Fin n, fixedPathRowAdmissible S j₀ rho i (A i)

/-- Step 5 of the article: unrestricted row-conditional tables factor
    into counts of independent rows. -/
theorem fixedPath_card_factor
    (S : Fin (d + 1) → Finset (Fin m))
    (j₀ : Fin m) (rho : Fin d ↪ Fin n) :
    (univ.filter (fun A : Table n m =>
      fixedPathRowwise S j₀ rho A)).card =
      ∏ i : Fin n,
        (univ.filter (fun row : Row m =>
          fixedPathRowAdmissible S j₀ rho i row)).card := by
  classical
  unfold fixedPathRowwise
  convert card_row_constraints_filter
    (fun i row => fixedPathRowAdmissible S j₀ rho i row)

/-- Steps 4--5 combined: injectivity corrected by partition Möbius
    weights and then factored row by row. -/
theorem fixedPath_mobius_factor
    (S : Fin (d + 1) → Finset (Fin m))
    (j₀ : Fin m) (rho : Fin d ↪ Fin n) :
    (∑ A : Table n m,
      if fixedPathRowwise S j₀ rho A ∧ DistinctColumns A then
        (1 : ℤ) else 0) =
    ∑ c : OrderedFinpartition m,
      mu c * ∏ i : Fin n,
        ((univ.filter (fun row : Row m =>
          fixedPathRowAdmissible S j₀ rho i row ∧ ConstOn c row)).card : ℤ) := by
  classical
  unfold fixedPathRowwise
  convert card_valid_with_row_constraints
    (fun i row => fixedPathRowAdmissible S j₀ rho i row)

end GradientKey.Concrete
