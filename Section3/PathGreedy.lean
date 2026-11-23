import PathShape

/-!
# Proposition 3.2: single-step greedy characterization

The selected row is exactly the first row with maximal quality.
Thus a fixed split `S -> T` at row `r` is equivalent to its bit-class
condition and strict quality bounds before `r`, weak bounds after `r`.
These are the article's rowwise conditions, before replacing the selected
quality by `q_j = min(a_j,s_(j+1))`.
-/

noncomputable section

namespace GradientKey.Concrete

open Finset

variable {n m : ℕ}

/-- The first maximum of `quality` is characterized by exactly the
    article's strict-before/weak-after comparison. -/
theorem greedyRow_eq_of_quality_order (A : Table n m)
    (S : Finset (Fin m)) (hn : 0 < n) (r : Fin n)
    (hmax : ∀ t : Fin n, quality A S t ≤ quality A S r)
    (hbefore : ∀ t : Fin n, t < r → quality A S t < quality A S r) :
    greedyRow A S hn = r := by
  have hgr : greedyRow A S hn ≤ r :=
    p1_greedy_first_max A S hn r (hmax _)
  have hnotlt : ¬ greedyRow A S hn < r := by
    intro h
    have hq := hbefore (greedyRow A S hn) h
    have hg := p1_greedy_quality_max A S hn r
    omega
  exact le_antisymm hgr (le_of_not_gt hnotlt)

/-- Row-wise requirements for the greedy algorithm to test `r`,
    preserving the distinguished column `j` in the child set `T`. -/
def pathOneStepTest (A : Table n m) (S T : Finset (Fin m))
    (j : Fin m) (r : Fin n) : Prop :=
  T = S.filter (fun k => A r k = A r j) ∧
  (∀ t : Fin n, t < r → quality A S t < quality A S r) ∧
  (∀ t : Fin n, r < t → quality A S t ≤ quality A S r)

/-- Exact per-step equivalence, including tie breaking. -/
theorem pathOneStepTest_iff (A : Table n m)
    (S T : Finset (Fin m)) (j : Fin m)
    (hn : 0 < n) (r : Fin n) (hS : 2 ≤ S.card) :
    pathOneStepTest A S T j r ↔
      greedyRow A S hn = r ∧ candidateStep A S j hn = T := by
  classical
  constructor
  · rintro ⟨hT, hbefore, hafter⟩
    have hmax : ∀ t : Fin n, quality A S t ≤ quality A S r := by
      intro t
      rcases lt_trichotomy t r with hlt | heq | hgt
      · exact le_of_lt (hbefore t hlt)
      · rw [heq]
      · exact hafter t hgt
    have hgreedy := greedyRow_eq_of_quality_order A S hn r hmax hbefore
    refine ⟨hgreedy, ?_⟩
    simpa [candidateStep, show ¬S.card ≤ 1 by omega, hgreedy] using hT.symm
  · rintro ⟨hgreedy, hT⟩
    have hmax : ∀ t : Fin n, quality A S t ≤ quality A S r := by
      intro t
      simpa only [hgreedy] using p1_greedy_quality_max A S hn t
    have hbefore : ∀ t : Fin n, t < r → quality A S t < quality A S r := by
      intro t ht
      by_contra hnot
      have hrev : quality A S r ≤ quality A S t := by omega
      have hfirst := p1_greedy_first_max A S hn t (by
        simpa only [hgreedy] using hrev)
      rw [hgreedy] at hfirst
      omega
    have hfilter : T = S.filter (fun k => A r k = A r j) := by
      calc
        T = candidateStep A S j hn := hT.symm
        _ = S.filter (fun k => A r k = A r j) := by
          simp [candidateStep, show ¬S.card ≤ 1 by omega, hgreedy]
    exact ⟨hfilter, hbefore, fun t _ => hmax t⟩

end GradientKey.Concrete
