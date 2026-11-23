import Counting

/-!
# Proposition 3.1: exact fork-counting reduction

This is the first (enumerative) step of Proposition 3.1, not the full
chain/partition path formula.  It uses the existing `tG`, `leafDepth`,
`candidateAt` and `ValidTable` without redefining any of them.

The result is valid even when there are no injective tables: both sides
are then zero under Lean's total division convention.

-/

noncomputable section

namespace GradientKey.Concrete

open Finset

variable {n m : ℕ}

/-- Number of valid tables for which the distinguished column `j`
    encounters a fork at depth `i`. -/
def forkTableCount (n m : ℕ) (hn : 0 < n)
    (j : Fin m) (i : ℕ) : ℕ :=
  (univ.filter (fun A : ValidTable n m =>
    2 ≤ (candidateAt A.1 j hn i).card)).card

/-- On a valid table, all forks occur before depth `n`. -/
theorem fork_depth_lt_n (A : ValidTable n m) (hn : 0 < n)
    (j : Fin m) (i : ℕ)
    (h : 2 ≤ (candidateAt A.1 j hn i).card) : i < n := by
  by_contra hni
  rw [p1_terminated_after_n A.1 A.2 j hn i (by omega)] at h
  simp at h

/-- Express leaf depth as a finite sum of fork indicators. -/
theorem leafDepth_eq_sum_fork_indicators (A : ValidTable n m)
    (hn : 0 < n) (j : Fin m) :
    leafDepth A.1 hn j =
      ∑ i ∈ range n, if 2 ≤ (candidateAt A.1 j hn i).card then 1 else 0 := by
  classical
  unfold leafDepth
  have hset :
      {i : ℕ | 2 ≤ (candidateAt A.1 j hn i).card} =
        ↑((range n).filter (fun i =>
          2 ≤ (candidateAt A.1 j hn i).card)) := by
    ext i
    simp only [Set.mem_setOf_eq, Finset.coe_filter, Finset.mem_range]
    constructor
    · intro hi
      exact ⟨fork_depth_lt_n A hn j i hi, hi⟩
    · exact fun hi => hi.2
  rw [hset, Set.ncard_coe_finset, Finset.card_filter]

/-- Sum over valid tables of one column's depth = sum of counts
    of valid tables with a fork at each depth. -/
theorem sum_leafDepth_eq_sum_forkTableCount
    (hn : 0 < n) (j : Fin m) :
    (∑ A : ValidTable n m, leafDepth A.1 hn j) =
      ∑ i ∈ range n, forkTableCount n m hn j i := by
  classical
  calc
    _ = ∑ A : ValidTable n m,
          ∑ i ∈ range n,
            if 2 ≤ (candidateAt A.1 j hn i).card then 1 else 0 := by
          apply Finset.sum_congr rfl
          intro A _
          exact leafDepth_eq_sum_fork_indicators A hn j
    _ = ∑ i ∈ range n,
          ∑ A : ValidTable n m,
            if 2 ≤ (candidateAt A.1 j hn i).card then 1 else 0 := by
          rw [Finset.sum_comm]
    _ = ∑ i ∈ range n, forkTableCount n m hn j i := by
          apply Finset.sum_congr rfl
          intro i _
          simp only [forkTableCount, Finset.card_filter]

/-- First counting identity behind Proposition 3.1, connected to
    the existing `tG`.  The path/partition formula will replace
    each `forkTableCount` by its chain/partition expansion. -/
theorem tG_eq_forkTableCounts (hn : 0 < n) (hm : 2 ≤ m) :
    tG n m hn =
      (∑ j : Fin m, ∑ i ∈ range n,
          (forkTableCount n m hn j i : ℝ)) /
        ((m : ℝ) * ((2 ^ n).descFactorial m : ℝ)) := by
  classical
  unfold tG cost
  rw [← Finset.sum_div, div_div, card_valid]
  rw [Finset.sum_comm]
  congr 1
  apply Finset.sum_congr rfl
  intro j _
  calc
    (∑ A : ValidTable n m, (leafDepth A.1 hn j : ℝ)) =
        ((∑ A : ValidTable n m, leafDepth A.1 hn j : ℕ) : ℝ) := by
          norm_cast
    _ = ((∑ i ∈ range n, forkTableCount n m hn j i : ℕ) : ℝ) := by
          rw [sum_leafDepth_eq_sum_forkTableCount hn j]
    _ = ∑ i ∈ range n, (forkTableCount n m hn j i : ℝ) := by
          norm_cast

end GradientKey.Concrete
