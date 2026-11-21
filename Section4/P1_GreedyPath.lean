import GradientKeySection4

/-!
P1: concrete greedy-path invariants.

STATUS: NOT COMPILED (no Lean, lake, or installed Mathlib in the runtime).
This file imports the unchanged v4 candidate baseline. All declarations below are
proof attempts, not verified theorem claims. The mathematical content is tied
to the baseline's `candidateStep`, `candidateAt`, and `pathDepth` definitions.
-/

noncomputable section

namespace GradientKey.Concrete

variable {n m : ℕ}

/-- Every transition takes a subset of the current candidate set. -/
theorem p1_step_subset (A : Table n m) (S : Finset (Fin m))
    (j : Fin m) (hn : 0 < n) : candidateStep A S j hn ⊆ S := by
  classical
  by_cases hs : S.card ≤ 1
  · simp [candidateStep, hs]
  · simpa [candidateStep, hs] using
      (Finset.filter_subset
        (fun k => A (greedyRow A S hn) k = A (greedyRow A S hn) j) S)

/-- The target column survives each transition. -/
theorem p1_step_mem (A : Table n m) (S : Finset (Fin m))
    (j : Fin m) (hn : 0 < n) (hj : j ∈ S) :
    j ∈ candidateStep A S j hn := by
  classical
  by_cases hs : S.card ≤ 1
  · simpa [candidateStep, hs] using hj
  · simp [candidateStep, hs, hj]

/-- The target column survives every depth, including beyond the leaf. -/
theorem p1_candidate_mem (A : Table n m) (j : Fin m)
    (hn : 0 < n) (i : ℕ) : j ∈ candidateAt A j hn i := by
  induction i with
  | zero => simp [candidateAt]
  | succ i ih =>
      change j ∈ candidateStep A (candidateAt A j hn i) j hn
      exact p1_step_mem A _ j hn ih

/-- Candidate sets are nested in the depth parameter. -/
theorem p1_candidate_subset_succ (A : Table n m) (j : Fin m)
    (hn : 0 < n) (i : ℕ) :
    candidateAt A j hn (i + 1) ⊆ candidateAt A j hn i := by
  change candidateStep A (candidateAt A j hn i) j hn ⊆ _
  exact p1_step_subset A _ j hn

theorem p1_candidate_subset_of_le (A : Table n m) (j : Fin m)
    (hn : 0 < n) {i k : ℕ} (hik : i ≤ k) :
    candidateAt A j hn k ⊆ candidateAt A j hn i := by
  induction k, hik using Nat.le_induction with
  | base => exact Finset.Subset.refl _
  | succ k _ ih => exact (p1_candidate_subset_succ A j hn k).trans ih

/-- No candidate set is empty, even after the path terminates. -/
theorem p1_candidate_nonempty (A : Table n m) (j : Fin m)
    (hn : 0 < n) (i : ℕ) :
    (candidateAt A j hn i).Nonempty :=
  ⟨j, p1_candidate_mem A j hn i⟩

/-- Candidate sets with at most one member are exactly the target singleton. -/
theorem p1_candidate_singleton_of_card_le_one
    (A : Table n m) (j : Fin m) (hn : 0 < n) (i : ℕ)
    (hs : (candidateAt A j hn i).card ≤ 1) :
    candidateAt A j hn i = {j} := by
  classical
  apply Finset.Subset.antisymm
  · intro k hk
    have hkj := (Finset.card_le_one_iff.mp hs) hk
      (p1_candidate_mem A j hn i)
    simpa using hkj
  · simp [p1_candidate_mem A j hn i]

/-- Once the path reaches a singleton, every later candidate set is that singleton. -/
theorem p1_candidate_stays_singleton (A : Table n m) (j : Fin m)
    (hn : 0 < n) (i k : ℕ)
    (hi : (candidateAt A j hn i).card ≤ 1) (hik : i ≤ k) :
    candidateAt A j hn k = {j} := by
  have hsub := p1_candidate_subset_of_le A j hn hik
  have hs : candidateAt A j hn i = {j} :=
    p1_candidate_singleton_of_card_le_one A j hn i hi
  apply Finset.Subset.antisymm
  · exact hsub.trans (le_of_eq hs)
  · simp [p1_candidate_mem A j hn k]

/-- The actual greedy choice dominates every original row's quality. -/
theorem p1_argmax_some (A : Table n m) (S : Finset (Fin m))
    (hn : 0 < n) :
    List.argmax (quality A S) (List.finRange n) =
      some (greedyRow A S hn) := by
  classical
  have hne : (List.finRange n) ≠ [] := by
    intro he
    have hmem : (⟨0, hn⟩ : Fin n) ∈ List.finRange n :=
      List.mem_finRange _
    simp [he] at hmem
  cases harg : List.argmax (quality A S) (List.finRange n) with
  | none =>
      have hempty := (List.argmax_eq_none).mp harg
      exact False.elim (hne hempty)
  | some r => simp [greedyRow, harg]

theorem p1_greedy_quality_max (A : Table n m) (S : Finset (Fin m))
    (hn : 0 < n) (r : Fin n) :
    quality A S r ≤ quality A S (greedyRow A S hn) := by
  classical
  have hm : greedyRow A S hn ∈
      List.argmax (quality A S) (List.finRange n) := by
    rw [p1_argmax_some A S hn]
    simp
  exact List.le_of_mem_argmax (List.mem_finRange r) hm

/-- Exact tie-breaking: a row whose quality matches the winning quality
cannot precede the selected row. -/
theorem p1_greedy_first_max (A : Table n m) (S : Finset (Fin m))
    (hn : 0 < n) (r : Fin n)
    (h : quality A S (greedyRow A S hn) ≤ quality A S r) :
    greedyRow A S hn ≤ r := by
  classical
  have hm : greedyRow A S hn ∈
      List.argmax (quality A S) (List.finRange n) := by
    rw [p1_argmax_some A S hn]
    simp
  have hi := List.index_of_argmax hm h
  simp only [List.idxOf_finRange] at hi
  exact hi

/-- If a row distinguishes the target from a candidate, both its bit
classes are nonempty; equivalently its quality is positive. -/
theorem p1_quality_pos_of_diff (A : Table n m) (S : Finset (Fin m))
    (r : Fin n) (j k : Fin m) (hj : j ∈ S) (hk : k ∈ S)
    (hd : A r k ≠ A r j) : 0 < quality A S r := by
  classical
  have hone : 0 < ones A S r := by
    unfold ones
    apply Finset.card_pos.mpr
    by_cases hjb : A r j = true
    · exact ⟨j, Finset.mem_filter.mpr ⟨hj, hjb⟩⟩
    · have hkb : A r k = true := by
        cases h1 : A r j <;> cases h2 : A r k <;>
          simp_all
      exact ⟨k, Finset.mem_filter.mpr ⟨hk, hkb⟩⟩
  have hzero : 0 < zeros A S r := by
    unfold zeros
    apply Finset.card_pos.mpr
    by_cases hjb : A r j = false
    · exact ⟨j, Finset.mem_filter.mpr ⟨hj, hjb⟩⟩
    · have hkb : A r k = false := by
        cases h1 : A r j <;> cases h2 : A r k <;>
          simp_all
      exact ⟨k, Finset.mem_filter.mpr ⟨hk, hkb⟩⟩
  exact lt_min_iff.mpr ⟨hone, hzero⟩

/-- Distinct columns force a positive-quality row on any non-singleton
candidate set containing the chosen column. -/
theorem p1_exists_positive_row (A : Table n m) (hA : DistinctColumns A)
    (S : Finset (Fin m)) (j : Fin m) (hj : j ∈ S)
    (hs : 2 ≤ S.card) :
    ∃ r : Fin n, 0 < quality A S r := by
  obtain ⟨k, hk, hkj⟩ :=
    Finset.exists_mem_ne (by omega : 1 < S.card) j
  have hcol : (fun r : Fin n => A r k) ≠ (fun r => A r j) := by
    intro heq
    exact hkj (hA heq)
  have hrow : ∃ r : Fin n, A r k ≠ A r j := by
    by_contra h
    push_neg at h
    apply hcol
    funext r
    exact h r
  obtain ⟨r, hr⟩ := hrow
  exact ⟨r, p1_quality_pos_of_diff A S r j k hj hk hr⟩

theorem p1_greedy_quality_pos (A : Table n m) (hA : DistinctColumns A)
    (S : Finset (Fin m)) (j : Fin m) (hn : 0 < n)
    (hj : j ∈ S) (hs : 2 ≤ S.card) :
    0 < quality A S (greedyRow A S hn) := by
  obtain ⟨r, hr⟩ := p1_exists_positive_row A hA S j hj hs
  exact lt_of_lt_of_le hr (p1_greedy_quality_max A S hn r)

/-- A positive-quality test has a candidate with the opposite bit from j. -/
theorem p1_opposite_of_quality_pos (A : Table n m)
    (S : Finset (Fin m)) (r : Fin n) (j : Fin m)
    (hq : 0 < quality A S r) :
    ∃ k ∈ S, A r k ≠ A r j := by
  classical
  have hone : 0 < ones A S r := (lt_min_iff.mp hq).1
  have hzero : 0 < zeros A S r := (lt_min_iff.mp hq).2
  cases hj : A r j with
  | false =>
      obtain ⟨k, hk⟩ := Finset.card_pos.mp hone
      have hk' : k ∈ S ∧ A r k = true := by
        simpa only [ones, Finset.mem_filter] using hk
      exact ⟨k, hk'.1, by simp [hk'.2, hj]⟩
  | true =>
      obtain ⟨k, hk⟩ := Finset.card_pos.mp hzero
      have hk' : k ∈ S ∧ A r k = false := by
        simpa only [zeros, Finset.mem_filter] using hk
      exact ⟨k, hk'.1, by simp [hk'.2, hj]⟩

/-- A greedy fork really removes at least one column. -/
theorem p1_greedy_step_card_lt (A : Table n m)
    (hA : DistinctColumns A) (S : Finset (Fin m)) (j : Fin m)
    (hn : 0 < n) (hj : j ∈ S) (hs : 2 ≤ S.card) :
    (candidateStep A S j hn).card < S.card := by
  classical
  let r := greedyRow A S hn
  have hq : 0 < quality A S r :=
    p1_greedy_quality_pos A hA S j hn hj hs
  obtain ⟨k, hk, hdiff⟩ := p1_opposite_of_quality_pos A S r j hq
  have hnot : k ∉ candidateStep A S j hn := by
    intro hmem
    have hbits : A r k = A r j := by
      have hmem' : k ∈ S ∧ A r k = A r j := by
        simpa [candidateStep, show ¬S.card ≤ 1 by omega, r] using hmem
      exact hmem'.2
    exact hdiff hbits
  have hsub : candidateStep A S j hn ⊂ S := by
    apply lt_of_le_of_ne (p1_step_subset A S j hn)
    intro heq
    rw [heq] at hnot
    exact hnot hk
  exact Finset.card_lt_card hsub

/-- A fork decreases candidate-set size, while the singleton case stays put. -/
theorem p1_path_card_step (A : Table n m) (hA : DistinctColumns A)
    (j : Fin m) (hn : 0 < n) (i : ℕ) :
    (if 2 ≤ (candidateAt A j hn i).card then 1 else 0) +
      (candidateAt A j hn (i + 1)).card ≤
      (candidateAt A j hn i).card := by
  classical
  by_cases hs : 2 ≤ (candidateAt A j hn i).card
  · have hlt := p1_greedy_step_card_lt A hA
      (candidateAt A j hn i) j hn (p1_candidate_mem A j hn i) hs
    change (if 2 ≤ (candidateAt A j hn i).card then 1 else 0) +
        (candidateStep A (candidateAt A j hn i) j hn).card ≤ _
    simp only [if_pos hs]
    omega
  · have hle : (candidateAt A j hn i).card ≤ 1 := by omega
    change (if 2 ≤ (candidateAt A j hn i).card then 1 else 0) +
        (candidateStep A (candidateAt A j hn i) j hn).card ≤ _
    simp [hs, candidateStep, hle]

/-- The row selected at a fork is constant on all its descendants. This
also holds at singleton nodes (where there is no actual test). -/
theorem p1_step_selected_constant (A : Table n m) (S : Finset (Fin m))
    (j k : Fin m) (hn : 0 < n) (hj : j ∈ S)
    (hk : k ∈ candidateStep A S j hn) :
    A (greedyRow A S hn) k = A (greedyRow A S hn) j := by
  classical
  by_cases hs : S.card ≤ 1
  · have hkS : k ∈ S := (p1_step_subset A S j hn) hk
    have hkj := (Finset.card_le_one_iff.mp hs) hkS hj
    rw [hkj]
  · have hk' : k ∈ S ∧
        A (greedyRow A S hn) k = A (greedyRow A S hn) j := by
        simpa [candidateStep, hs] using hk
    exact hk'.2

/-- The finite set of rows not yet known to be constant on S. -/
def p1_activeRows (A : Table n m) (S : Finset (Fin m))
    (j : Fin m) : Finset (Fin n) := by
  classical
  exact Finset.univ.filter (fun r => ∃ k ∈ S, A r k ≠ A r j)

/-- If candidates shrink, the set of potentially distinguishing rows shrinks. -/
theorem p1_activeRows_anti (A : Table n m)
    (S T : Finset (Fin m)) (j : Fin m) (hTS : T ⊆ S) :
    p1_activeRows A T j ⊆ p1_activeRows A S j := by
  classical
  intro r hr
  obtain ⟨k, hk, hd⟩ := (Finset.mem_filter.mp hr).2
  exact Finset.mem_filter.mpr ⟨Finset.mem_univ r,
    ⟨k, hTS hk, hd⟩⟩

/-- A row becomes inactive immediately after it is selected. -/
theorem p1_selected_inactive_after_step (A : Table n m)
    (S : Finset (Fin m)) (j : Fin m) (hn : 0 < n)
    (hj : j ∈ S) :
    greedyRow A S hn ∉ p1_activeRows A (candidateStep A S j hn) j := by
  classical
  intro h
  obtain ⟨k, hk, hdiff⟩ := (Finset.mem_filter.mp h).2
  exact hdiff (p1_step_selected_constant A S j k hn hj hk)

/-- A non-singleton candidate set has an active row, and the greedy row
is one of them. -/
theorem p1_selected_active_at_fork (A : Table n m)
    (hA : DistinctColumns A) (S : Finset (Fin m))
    (j : Fin m) (hn : 0 < n) (hj : j ∈ S) (hs : 2 ≤ S.card) :
    greedyRow A S hn ∈ p1_activeRows A S j := by
  classical
  obtain ⟨k, hk, hd⟩ := p1_opposite_of_quality_pos A S
    (greedyRow A S hn) j
    (p1_greedy_quality_pos A hA S j hn hj hs)
  exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, ⟨k, hk, hd⟩⟩

/-- At each fork the number of active rows strictly decreases. -/
theorem p1_activeRows_card_lt_at_fork (A : Table n m)
    (hA : DistinctColumns A) (S : Finset (Fin m))
    (j : Fin m) (hn : 0 < n) (hj : j ∈ S) (hs : 2 ≤ S.card) :
    (p1_activeRows A (candidateStep A S j hn) j).card <
      (p1_activeRows A S j).card := by
  have hsub := p1_activeRows_anti A S (candidateStep A S j hn)
    j (p1_step_subset A S j hn)
  have hproper : p1_activeRows A (candidateStep A S j hn) j ⊂
      p1_activeRows A S j := by
    apply lt_of_le_of_ne hsub
    intro heq
    have hmem := p1_selected_active_at_fork A hA S j hn hj hs
    have hmem' : greedyRow A S hn ∈
        p1_activeRows A (candidateStep A S j hn) j := by
      simpa only [heq] using hmem
    exact (p1_selected_inactive_after_step A S j hn hj) hmem'
  exact Finset.card_lt_card hproper

/-- In particular, a previously selected row cannot be selected at a later
fork: that row is already constant on all remaining candidate columns. -/
theorem p1_no_row_reuse (A : Table n m) (hA : DistinctColumns A)
    (j : Fin m) (hn : 0 < n) {i t : ℕ} (hit : i < t)
    (ht : 2 ≤ (candidateAt A j hn t).card) :
    greedyRow A (candidateAt A j hn i) hn ≠
      greedyRow A (candidateAt A j hn t) hn := by
  let S := candidateAt A j hn i
  let T := candidateAt A j hn t
  let r := greedyRow A S hn
  have hconst : ∀ k ∈ T, A r k = A r j := by
    intro k hk
    have hchild : k ∈ candidateAt A j hn (i+1) :=
      (p1_candidate_subset_of_le A j hn (Nat.succ_le_of_lt hit)) hk
    exact p1_step_selected_constant A S j k hn
      (p1_candidate_mem A j hn i) hchild
  have hnot : r ∉ p1_activeRows A T j := by
    intro hr
    obtain ⟨k, hk, hd⟩ := (Finset.mem_filter.mp hr).2
    exact hd (hconst k hk)
  intro heq
  have hactive : greedyRow A T hn ∈ p1_activeRows A T j :=
    p1_selected_active_at_fork A hA T j hn
      (p1_candidate_mem A j hn t) ht
  have hr : r = greedyRow A T hn := heq
  exact hnot (hr ▸ hactive)

/-- Nat-valued fork indicator for the concrete path. -/
private def p1_fork (A : Table n m) (j : Fin m) (hn : 0 < n)
    (i : ℕ) : ℕ :=
  if 2 ≤ (candidateAt A j hn i).card then 1 else 0

private def p1_forks (A : Table n m) (j : Fin m) (hn : 0 < n)
    (i : ℕ) : ℕ :=
  ∑ t ∈ Finset.range i, p1_fork A j hn t

/-- The invariant: used fork budget plus remaining candidate count is
nonincreasing. This is a telescoping statement in Nat, not probability. -/
theorem p1_candidate_budget_step (A : Table n m)
    (hA : DistinctColumns A) (j : Fin m) (hn : 0 < n) (i : ℕ) :
    p1_forks A j hn (i+1) + (candidateAt A j hn (i+1)).card ≤
      p1_forks A j hn i + (candidateAt A j hn i).card := by
  have hstep := p1_path_card_step A hA j hn i
  have hf : p1_forks A j hn (i+1) = p1_forks A j hn i + p1_fork A j hn i := by
    simp only [p1_forks, Finset.sum_range_succ]
  rw [hf]
  unfold p1_fork
  omega

/-- The same invariant between arbitrary depths. -/
theorem p1_candidate_budget_anti (A : Table n m)
    (hA : DistinctColumns A) (j : Fin m) (hn : 0 < n)
    {i t : ℕ} (hit : i ≤ t) :
    p1_forks A j hn t + (candidateAt A j hn t).card ≤
      p1_forks A j hn i + (candidateAt A j hn i).card := by
  induction t, hit using Nat.le_induction with
  | base => exact le_refl _
  | succ t _ ih => exact (p1_candidate_budget_step A hA j hn t).trans ih

/-- The prefix fork count is monotone because every summand is 0 or 1. -/
theorem p1_forks_mono (A : Table n m) (j : Fin m)
    (hn : 0 < n) {i t : ℕ} (hit : i ≤ t) :
    p1_forks A j hn i ≤ p1_forks A j hn t := by
  induction t, hit using Nat.le_induction with
  | base => exact le_refl _
  | succ t _ ih =>
      have hstep : p1_forks A j hn t ≤ p1_forks A j hn (t+1) := by
        simp only [p1_forks, Finset.sum_range_succ]
        omega
      exact le_trans ih hstep

/-- At a fork, one active row is consumed. At a leaf no active rows
can be added: the candidate set never grows. -/
theorem p1_activeRows_step_budget (A : Table n m)
    (hA : DistinctColumns A) (j : Fin m) (hn : 0 < n) (i : ℕ) :
    p1_fork A j hn i +
        (p1_activeRows A (candidateAt A j hn (i+1)) j).card ≤
        (p1_activeRows A (candidateAt A j hn i) j).card := by
  classical
  have hsub := p1_activeRows_anti A
    (candidateAt A j hn i) (candidateAt A j hn (i+1)) j
    (p1_candidate_subset_succ A j hn i)
  have hweak := Finset.card_le_card hsub
  by_cases hs : 2 ≤ (candidateAt A j hn i).card
  · have hstrict := p1_activeRows_card_lt_at_fork A hA
      (candidateAt A j hn i) j hn (p1_candidate_mem A j hn i) hs
    have hstrict' :
        (p1_activeRows A (candidateAt A j hn (i+1)) j).card <
        (p1_activeRows A (candidateAt A j hn i) j).card := hstrict
    simp only [p1_fork, if_pos hs]
    omega
  · simp only [p1_fork, if_neg hs]
    omega

/-- The number of forks used plus the number of rows still capable
of distinguishing the remaining candidates is bounded by n. -/
theorem p1_activeRows_budget (A : Table n m)
    (hA : DistinctColumns A) (j : Fin m) (hn : 0 < n) (i : ℕ) :
    p1_forks A j hn i +
        (p1_activeRows A (candidateAt A j hn i) j).card ≤ n := by
  induction i with
  | zero =>
      have hsub : p1_activeRows A (candidateAt A j hn 0) j ⊆
          (Finset.univ : Finset (Fin n)) := Finset.subset_univ _
      have hcard := Finset.card_le_card hsub
      simpa [p1_forks] using hcard
  | succ i ih =>
      have hs := p1_activeRows_step_budget A hA j hn i
      have hforks : p1_forks A j hn (i+1) =
          p1_forks A j hn i + p1_fork A j hn i := by
        simp [p1_forks, Finset.sum_range_succ]
      rw [hforks]
      omega

/-- Every valid table reaches the selected singleton at or before
step n, including m = 2^n and n = 1. -/
theorem p1_terminates_by_n (A : Table n m) (hA : DistinctColumns A)
    (j : Fin m) (hn : 0 < n) :
    candidateAt A j hn n = {j} := by
  classical
  by_contra hne
  have hfork : 2 ≤ (candidateAt A j hn n).card := by
    have hpos : 1 ≤ (candidateAt A j hn n).card :=
      Finset.card_pos.mpr (p1_candidate_nonempty A j hn n)
    have hnotle : ¬(candidateAt A j hn n).card ≤ 1 := by
      intro hle
      exact hne (p1_candidate_singleton_of_card_le_one A j hn n hle)
    omega
  have hbefore : ∀ i < n, 2 ≤ (candidateAt A j hn i).card := by
    intro i hi
    have hsub := p1_candidate_subset_of_le A j hn (Nat.le_of_lt hi)
    have hle := Finset.card_le_card hsub
    omega
  have hcount : p1_forks A j hn n = n := by
    unfold p1_forks
    calc
      (∑ i ∈ Finset.range n, p1_fork A j hn i) =
          ∑ i ∈ Finset.range n, (1 : ℕ) := by
            apply Finset.sum_congr rfl
            intro i hi
            simp [p1_fork, hbefore i (Finset.mem_range.mp hi)]
      _ = n := by simp
  have hactive : 0 <
      (p1_activeRows A (candidateAt A j hn n) j).card := by
    exact Finset.card_pos.mpr
      ⟨greedyRow A (candidateAt A j hn n) hn,
       p1_selected_active_at_fork A hA _ j hn
         (p1_candidate_mem A j hn n) hfork⟩
  have hbudget := p1_activeRows_budget A hA j hn n
  omega

/-- No forks remain after time n. -/
theorem p1_terminated_after_n (A : Table n m)
    (hA : DistinctColumns A) (j : Fin m) (hn : 0 < n)
    (i : ℕ) (hi : n ≤ i) :
    candidateAt A j hn i = {j} := by
  exact p1_candidate_stays_singleton A j hn n i
    (by rw [p1_terminates_by_n A hA j hn]; simp) hi

/-- All fork indicators vanish from n onward. -/
theorem p1_no_forks_after_n (A : Table n m)
    (hA : DistinctColumns A) (j : Fin m) (hn : 0 < n)
    (i : ℕ) (hi : n ≤ i) : p1_fork A j hn i = 0 := by
  simp [p1_fork, p1_terminated_after_n A hA j hn i hi]

/-- Any prefix extending beyond n counts exactly the actual path forks.
Together with p1_depth_eq_forks, this identifies pathDepth with the
complete decision-tree depth of column j. -/
theorem p1_forks_stabilize (A : Table n m)
    (hA : DistinctColumns A) (j : Fin m) (hn : 0 < n)
    (i : ℕ) (hi : n ≤ i) :
    p1_forks A j hn i = p1_forks A j hn n := by
  induction i, hi using Nat.le_induction with
  | base => rfl
  | succ i hni ih =>
      have hzero : p1_fork A j hn i = 0 :=
        p1_no_forks_after_n A hA j hn i hni
      have heq : p1_forks A j hn (i+1) = p1_forks A j hn i := by
        simp only [p1_forks, Finset.sum_range_succ, hzero, add_zero]
      exact heq.trans ih

/-- Pointwise tail bound, valid at every cutoff h (also h > n). -/
theorem p1_path_tail_nat (A : Table n m) (hA : DistinctColumns A)
    (j : Fin m) (hn : 0 < n) (h : ℕ) :
    p1_forks A j hn n + 1 ≤
      p1_forks A j hn h + (candidateAt A j hn h).card := by
  by_cases hle : h ≤ n
  · have hbudget := p1_candidate_budget_anti A hA j hn hle
    have hnonempty : 1 ≤ (candidateAt A j hn n).card :=
      Finset.card_pos.mpr (p1_candidate_nonempty A j hn n)
    omega
  · have hle' : n ≤ h := by omega
    have hmono := p1_forks_mono A j hn hle'
    have hnonempty : 1 ≤ (candidateAt A j hn h).card :=
      Finset.card_pos.mpr (p1_candidate_nonempty A j hn h)
    omega

/-- The concrete `pathDepth` is the count of the first n fork indicators. -/
theorem p1_depth_eq_forks (A : Table n m) (j : Fin m)
    (hn : 0 < n) :
    pathDepth A j hn = (p1_forks A j hn n : ℝ) := by
  classical
  simp [pathDepth, p1_forks, p1_fork, Finset.sum_ite]

/-- The definition of pathDepth agrees with the complete fork count:
there are no additional forks after depth n. -/
theorem p1_depth_equals_complete_path (A : Table n m)
    (hA : DistinctColumns A) (j : Fin m) (hn : 0 < n)
    (h : ℕ) (hh : n ≤ h) :
    pathDepth A j hn = (p1_forks A j hn h : ℝ) := by
  rw [p1_depth_eq_forks, p1_forks_stabilize A hA j hn h hh]

/-- A concrete instance of Lemma 4.1's deterministic path-tail inequality. -/
theorem p1_sample_hTail (hn : 0 < n) (ω : Sample n m) (h : ℕ) :
    sampleDepth hn ω ≤
      (∑ i ∈ Finset.range h,
        if 2 ≤ sampleSize hn ω i then (1 : ℝ) else 0) +
      ((sampleSize hn ω h : ℝ) - 1) := by
  have hnat := p1_path_tail_nat ω.1.1 ω.1.2 ω.2 hn h
  have hreal : (p1_forks ω.1.1 ω.2 hn n : ℝ) + 1 ≤
      (p1_forks ω.1.1 ω.2 hn h : ℝ) +
      ((candidateAt ω.1.1 ω.2 hn h).card : ℝ) := by
    exact_mod_cast hnat
  have hdepth : sampleDepth hn ω =
      (p1_forks ω.1.1 ω.2 hn n : ℝ) :=
    p1_depth_eq_forks ω.1.1 ω.2 hn
  have hsum : (p1_forks ω.1.1 ω.2 hn h : ℝ) =
      ∑ i ∈ Finset.range h,
        if 2 ≤ sampleSize hn ω i then (1 : ℝ) else 0 := by
    unfold p1_forks p1_fork sampleSize
    push_cast
    rfl
  rw [hdepth, ← hsum]
  have hss : (sampleSize hn ω h : ℝ) =
      ((candidateAt ω.1.1 ω.2 hn h).card : ℝ) := rfl
  rw [hss]
  linarith

/-- No assumed `hTail` is needed by clients of the concrete sample space. -/
noncomputable def p1_finitePathData (hn : 0 < n) :
    GradientKey.FinitePathData (Sample n m) m :=
  finitePathData hn (p1_sample_hTail hn)

end GradientKey.Concrete
