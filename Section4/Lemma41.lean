import P1_GreedyPath
import P2_SizeRecurrence

/-!
# Lemma 4.1 for the concrete greedy path

Bridge from P2's finite partition identity to `Concrete.candidateAt`.
For a fixed table `A` and depth `i`, the key of a column `k` is its
candidate set `S_i(k)`, and its bit is the entry of the row tested at
`S_i(k)`.  The fibre of the key through `j` is `S_i(j)`, the refined
fibre is `S_{i+1}(j)`, and P2's imbalance is `localImbalance`.
Averaging over all (table, column) samples gives the recurrence
`e_{i+1} = (e_i - p_i + V_i)/2`.
-/

noncomputable section

namespace GradientKey.Concrete

open Finset

variable {n m : ℕ}

/-- The candidate sets at depth `i` partition the columns:
`k ∈ S_i(j)` iff `S_i(k) = S_i(j)`. -/
theorem mem_candidateAt_iff (A : Table n m) (hn : 0 < n) (i : ℕ)
    (j k : Fin m) :
    k ∈ candidateAt A j hn i ↔ candidateAt A k hn i = candidateAt A j hn i := by
  classical
  induction i generalizing j k with
  | zero => simp [candidateAt]
  | succ i ih =>
      constructor
      · intro hk
        have hkS : k ∈ candidateAt A j hn i :=
          p1_candidate_subset_succ A j hn i hk
        have hS : candidateAt A k hn i = candidateAt A j hn i := (ih j k).1 hkS
        change candidateStep A (candidateAt A k hn i) k hn =
          candidateStep A (candidateAt A j hn i) j hn
        change k ∈ candidateStep A (candidateAt A j hn i) j hn at hk
        rw [hS]
        unfold candidateStep at hk ⊢
        by_cases hc : (candidateAt A j hn i).card ≤ 1
        · simp only [if_pos hc]
        · rw [if_neg hc] at hk
          simp only [if_neg hc]
          have hbit := (Finset.mem_filter.mp hk).2
          ext x
          simp only [Finset.mem_filter, hbit]
      · intro h
        rw [← h]
        exact p1_candidate_mem A k hn (i + 1)

/-- The key used for depth `i`. -/
def depthKey (A : Table n m) (hn : 0 < n) (i : ℕ) : Fin m → Finset (Fin m) :=
  fun k => candidateAt A k hn i

/-- The bit of the row tested at the candidate set of each column. -/
def depthBit (A : Table n m) (hn : 0 < n) (i : ℕ) : Fin m → Bool :=
  fun k => A (greedyRow A (candidateAt A k hn i) hn) k

theorem fiber_depthKey (A : Table n m) (hn : 0 < n) (i : ℕ) (j : Fin m) :
    P2.fiber (depthKey A hn i) (depthKey A hn i j) = candidateAt A j hn i := by
  ext k
  unfold P2.fiber depthKey
  rw [Finset.mem_filter]
  simp only [Finset.mem_univ, true_and]
  exact (mem_candidateAt_iff A hn i j k).symm

theorem parentCount_depthKey (A : Table n m) (hn : 0 < n) (i : ℕ) (j : Fin m) :
    P2.parentCount (depthKey A hn i) (depthKey A hn i j) =
      (candidateAt A j hn i).card := by
  unfold P2.parentCount
  rw [fiber_depthKey]

theorem childCount_depthKey (A : Table n m) (hn : 0 < n) (i : ℕ) (j : Fin m) :
    P2.childCount (depthKey A hn i) (depthBit A hn i) j =
      (candidateAt A j hn (i + 1)).card := by
  classical
  unfold P2.childCount
  congr 1
  ext k
  simp only [P2.fiber, depthKey, depthBit, Finset.mem_filter, Finset.mem_univ,
    true_and, Prod.mk.injEq]
  change (candidateAt A k hn i = candidateAt A j hn i ∧ _) ↔
    k ∈ candidateStep A (candidateAt A j hn i) j hn
  constructor
  · rintro ⟨hS, hb⟩
    rw [hS] at hb
    have hkS : k ∈ candidateAt A j hn i := (mem_candidateAt_iff A hn i j k).2 hS
    unfold candidateStep
    by_cases hc : (candidateAt A j hn i).card ≤ 1
    · rw [if_pos hc]; exact hkS
    · rw [if_neg hc]; exact Finset.mem_filter.mpr ⟨hkS, hb⟩
  · intro hk
    have hkS : k ∈ candidateAt A j hn i := p1_step_subset A _ j hn hk
    have hS := (mem_candidateAt_iff A hn i j k).1 hkS
    refine ⟨hS, ?_⟩
    rw [hS]
    exact p1_step_selected_constant A _ j k hn (p1_candidate_mem A j hn i) hk

theorem forkFlag_depthKey (A : Table n m) (hn : 0 < n) (i : ℕ) (j : Fin m) :
    P2.forkFlag (depthKey A hn i) (depthKey A hn i j) =
      if 2 ≤ (candidateAt A j hn i).card then (1 : ℝ) else 0 := by
  unfold P2.forkFlag
  rw [parentCount_depthKey]

theorem imbalance_depthKey (A : Table n m) (hn : 0 < n) (i : ℕ) (j : Fin m) :
    P2.imbalance (depthKey A hn i) (depthBit A hn i) (depthKey A hn i j) =
      localImbalance A (candidateAt A j hn i) hn := by
  classical
  set S := candidateAt A j hn i with hSdef
  set g := greedyRow A S hn
  have hfib : P2.fiber (depthKey A hn i) (depthKey A hn i j) = S := fiber_depthKey A hn i j
  have hbitS : ∀ k ∈ S, depthBit A hn i k = A g k := by
    intro k hk
    have hS := (mem_candidateAt_iff A hn i j k).1 hk
    simp only [depthBit, hS, g, S]
  have htrue : P2.trueCount (depthKey A hn i) (depthBit A hn i) (depthKey A hn i j) =
      ones A S g := by
    unfold P2.trueCount ones
    rw [hfib]
    congr 1
    apply Finset.filter_congr
    intro k hk
    rw [hbitS k hk]
  have hfalse : P2.falseCount (depthKey A hn i) (depthBit A hn i) (depthKey A hn i j) =
      zeros A S g := by
    unfold P2.falseCount zeros
    rw [hfib]
    congr 1
    apply Finset.filter_congr
    intro k hk
    rw [hbitS k hk]
  have hsum : ones A S g + zeros A S g = S.card := by
    have h := P2.trueCount_add_falseCount (depthKey A hn i) (depthBit A hn i)
      (depthKey A hn i j)
    rw [htrue, hfalse, parentCount_depthKey] at h
    exact h
  unfold P2.imbalance localImbalance
  rw [parentCount_depthKey, htrue, hfalse]
  by_cases hc : 2 ≤ S.card
  · rw [if_pos hc, if_neg (by omega)]
    have hs : (S.card : ℝ) = (ones A S g : ℝ) + (zeros A S g : ℝ) := by
      exact_mod_cast hsum.symm
    congr 1
    rw [hs]
    ring
  · rw [if_neg hc, if_pos (by omega)]

/-- Lemma 4.1 for one fixed table, summed over the columns. -/
theorem table_size_recurrence (A : Table n m) (hn : 0 < n) (i : ℕ) :
    (∑ j : Fin m, (((candidateAt A j hn (i + 1)).card : ℝ) - 1)) =
      ((∑ j : Fin m, (((candidateAt A j hn i).card : ℝ) - 1)) -
        (∑ j : Fin m, if 2 ≤ (candidateAt A j hn i).card then (1 : ℝ) else 0) +
        (∑ j : Fin m, localImbalance A (candidateAt A j hn i) hn)) / 2 := by
  have h := P2.finite_partition_recurrence (depthKey A hn i) (depthBit A hn i)
  simp only [childCount_depthKey, parentCount_depthKey, forkFlag_depthKey,
    imbalance_depthKey] at h
  exact h

/-- The sum over the sample space is the double sum over tables and columns. -/
theorem sum_sample (f : Sample n m → ℝ) :
    (∑ ω : Sample n m, f ω) = ∑ A : ValidTable n m, ∑ j : Fin m, f (A, j) := by
  classical
  rw [← Finset.univ_product_univ, Finset.sum_product]

/-- Lemma 4.1 (recurrence) for the concrete greedy path. -/
theorem concrete_expectedExcess_succ (hn : 0 < n) [Nonempty (Sample n m)] (i : ℕ) :
    (p1_finitePathData (m := m) hn).expectedExcess (i + 1) =
      ((p1_finitePathData (m := m) hn).expectedExcess i -
        (p1_finitePathData (m := m) hn).forkProb i +
        (p1_finitePathData (m := m) hn).expectedImbalance i) / 2 := by
  unfold FinitePathData.expectedExcess FinitePathData.forkProb
    FinitePathData.expectedImbalance finiteAverage
  change (∑ ω : Sample n m, ((sampleSize hn ω (i + 1) : ℝ) - 1)) / _ =
    ((∑ ω : Sample n m, ((sampleSize hn ω i : ℝ) - 1)) / _ -
      (∑ ω : Sample n m, if 2 ≤ sampleSize hn ω i then (1 : ℝ) else 0) / _ +
      (∑ ω : Sample n m, sampleImbalance hn ω i) / _) / 2
  rw [sum_sample, sum_sample, sum_sample, sum_sample]
  simp only [sampleSize, sampleImbalance]
  have hA : ∀ A : ValidTable n m,
      (∑ j : Fin m, (((candidateAt A.1 j hn (i + 1)).card : ℝ) - 1)) =
      ((∑ j : Fin m, (((candidateAt A.1 j hn i).card : ℝ) - 1)) -
        (∑ j : Fin m, if 2 ≤ (candidateAt A.1 j hn i).card then (1 : ℝ) else 0) +
        (∑ j : Fin m, localImbalance A.1 (candidateAt A.1 j hn i) hn)) / 2 :=
    fun A => table_size_recurrence A.1 hn i
  rw [Finset.sum_congr rfl (fun A _ => hA A)]
  rw [← Finset.sum_div, Finset.sum_add_distrib, Finset.sum_sub_distrib]
  have key : ∀ X Y Z c : ℝ, (X - Y + Z) / 2 / c = (X / c - Y / c + Z / c) / 2 := by
    intros; ring
  exact key _ _ _ _

end GradientKey.Concrete
