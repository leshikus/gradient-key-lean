import PathDefs
import PathShape

/-!
# Proposition 3.1: map every genuine fork to its finite chain

The combinatorial RHS is indexed by `PathChain n m`, whose members
have `d<n` and a strictly decreasing vector of sizes. This module
constructs such an index from the actual `candidateAt` sets, without
postulating a chain hypothesis. It is used to group the fork count.

-/

noncomputable section

namespace GradientKey.Concrete

open Finset Classical

variable {n m : ℕ}

/-- At every depth, candidate-set cardinality is bounded by `m`. -/
def pathBoundedCard (A : Table n m) (hn : 0 < n)
    (j : Fin m) (i : ℕ) : Fin (m + 1) := by
  have hsub : candidateAt A j hn i ⊆ (univ : Finset (Fin m)) := by
    have h := p1_candidate_subset_of_le A j hn (Nat.zero_le i)
    simpa only [candidateAt] using h
  have hc := Finset.card_le_card hsub
  simp only [Finset.card_univ, Fintype.card_fin] at hc
  exact ⟨(candidateAt A j hn i).card, by omega⟩

/-- A genuine fork at depth `d` determines an article chain with
    sizes equal to the actual candidate-set cardinalities. -/
def pathChainOfFork (A : ValidTable n m) (hn : 0 < n)
    (j : Fin m) (d : ℕ)
    (hd : 2 ≤ (candidateAt A.1 j hn d).card) : PathChain n m := by
  let depth : Fin n := ⟨d, fork_depth_lt_n A hn j d hd⟩
  let sizes : PathSizeVector m d := fun i => pathBoundedCard A.1 hn j i.val
  refine ⟨⟨depth, sizes⟩, ?_⟩
  dsimp [IsPathChain]
  refine ⟨?_, ?_, ?_⟩
  · simp [sizes, pathBoundedCard, candidateAt]
  · simpa [sizes, pathBoundedCard] using hd
  · intro i
    have hstrict := pathCandidateSizes_step_lt A hn j d hd i
    exact hstrict

/-- The chain's depth agrees with the fork depth. -/
theorem pathChainOfFork_depth (A : ValidTable n m) (hn : 0 < n)
    (j : Fin m) (d : ℕ)
    (hd : 2 ≤ (candidateAt A.1 j hn d).card) :
    pathChainDepth (pathChainOfFork A hn j d hd) = d := rfl

/-- The chain records exactly the actual sizes, not an unrelated vector. -/
theorem pathChainOfFork_sizes (A : ValidTable n m) (hn : 0 < n)
    (j : Fin m) (d : ℕ)
    (hd : 2 ≤ (candidateAt A.1 j hn d).card)
    (i : Fin (d + 1)) :
    (pathChainSizes (pathChainOfFork A hn j d hd) i).val =
      (candidateAt A.1 j hn i.val).card := rfl

end GradientKey.Concrete
