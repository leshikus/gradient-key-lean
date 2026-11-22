import PathFork

/-!
# Proposition 3.1: shape of genuine candidate-set chains

A fork at depth `d` yields nested candidate sets
`S₀ ⊋ S₁ ⊋ ... ⊋ S_d`, all containing the distinguished column.
Their sizes are strictly decreasing, all at least two, and `d < n`.

Draft against Lean v4.36.0 and pinned Mathlib v4.36.0.
Compilation and axiom auditing have NOT been performed in this runtime.
-/

noncomputable section

namespace GradientKey.Concrete

open Finset

variable {n m : ℕ}

/-- The first `d+1` candidate sets of a distinguished column. -/
def pathCandidates (A : Table n m) (hn : 0 < n)
    (j : Fin m) (d : ℕ) : Fin (d + 1) → Finset (Fin m) :=
  fun i => candidateAt A j hn i.val

/-- The first `d+1` candidate sizes, as natural numbers. -/
def pathCandidateSizes (A : Table n m) (hn : 0 < n)
    (j : Fin m) (d : ℕ) : Fin (d + 1) → ℕ :=
  fun i => (pathCandidates A hn j d i).card

/-- The path begins at the entire column set. -/
theorem pathCandidates_zero (A : Table n m) (hn : 0 < n)
    (j : Fin m) (d : ℕ) :
    pathCandidates A hn j d ⟨0, Nat.zero_lt_succ d⟩ = univ := rfl

/-- Every candidate set contains its distinguished column. -/
theorem pathCandidates_mem (A : Table n m) (hn : 0 < n)
    (j : Fin m) (d : ℕ) (i : Fin (d + 1)) :
    j ∈ pathCandidates A hn j d i :=
  p1_candidate_mem A j hn i.val

/-- The path is nested, independently of column distinctness. -/
theorem pathCandidates_step_subset (A : Table n m) (hn : 0 < n)
    (j : Fin m) (d : ℕ) (i : Fin d) :
    pathCandidates A hn j d (Fin.succ i) ⊆
      pathCandidates A hn j d (Fin.castSucc i) := by
  exact p1_candidate_subset_succ A j hn i.val

/-- A later fork forces all previous candidate sets to have >=2 columns. -/
theorem pathCandidates_fork_before (A : ValidTable n m) (hn : 0 < n)
    (j : Fin m) (d : ℕ)
    (hd : 2 ≤ (candidateAt A.1 j hn d).card)
    (i : Fin (d + 1)) :
    2 ≤ (pathCandidates A.1 hn j d i).card := by
  have hsub : candidateAt A.1 j hn d ⊆
      candidateAt A.1 j hn i.val :=
    p1_candidate_subset_of_le A.1 j hn (by have := i.isLt; omega)
  exact hd.trans (Finset.card_le_card hsub)

/-- Candidate sizes drop strictly at every step before a later fork. -/
theorem pathCandidateSizes_step_lt (A : ValidTable n m) (hn : 0 < n)
    (j : Fin m) (d : ℕ)
    (hd : 2 ≤ (candidateAt A.1 j hn d).card)
    (i : Fin d) :
    pathCandidateSizes A.1 hn j d (Fin.succ i) <
      pathCandidateSizes A.1 hn j d (Fin.castSucc i) := by
  have hs : 2 ≤ (candidateAt A.1 j hn i.val).card :=
    pathCandidates_fork_before A hn j d hd (Fin.castSucc i)
  have hstep := p1_greedy_step_card_lt A.1 A.2
    (candidateAt A.1 j hn i.val) j hn
    (p1_candidate_mem A.1 j hn i.val) hs
  exact hstep

/-- Therefore the candidate sets form a genuinely strict chain. -/
theorem pathCandidates_step_ssubset (A : ValidTable n m) (hn : 0 < n)
    (j : Fin m) (d : ℕ)
    (hd : 2 ≤ (candidateAt A.1 j hn d).card)
    (i : Fin d) :
    pathCandidates A.1 hn j d (Fin.succ i) ⊂
      pathCandidates A.1 hn j d (Fin.castSucc i) := by
  apply lt_of_le_of_ne (pathCandidates_step_subset A.1 hn j d i)
  intro heq
  have hc := congrArg Finset.card heq
  have hlt := pathCandidateSizes_step_lt A hn j d hd i
  exact (Nat.ne_of_lt hlt) hc

/-- A fork of depth `d` must satisfy `d < n` (no row can be reused). -/
theorem pathFork_depth_lt_n (A : ValidTable n m) (hn : 0 < n)
    (j : Fin m) (d : ℕ)
    (hd : 2 ≤ (candidateAt A.1 j hn d).card) : d < n :=
  fork_depth_lt_n A hn j d hd

/-- Every fork also consumes at least `d+2` distinct columns. -/
theorem pathFork_size_budget (A : ValidTable n m) (hn : 0 < n)
    (j : Fin m) (d : ℕ)
    (hd : 2 ≤ (candidateAt A.1 j hn d).card) : d + 2 ≤ m := by
  have hfork : 2 ≤ (candFrom A.1 hn univ j d).card := by
    rw [← candidateAt_eq_candFrom]
    exact hd
  have hb := candFrom_fork_bound A.1 A.2 hn univ j (mem_univ j) d hfork
  simp only [Finset.card_univ, Fintype.card_fin] at hb
  omega

end GradientKey.Concrete
