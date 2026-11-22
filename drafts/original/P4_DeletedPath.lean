import Mathlib

/-!
# P4: greedy paths after deletion of a row (isolated module)

This module deliberately does not import the uncompiled v4 baseline.
Rows retain their *original* `Fin n` indices; deleting `r` means
restricting to `Finset.univ.erase r`. Thus ties continue to be resolved
in original row order, without relying on a reindexing convention.

The state explicitly tracks unused rows. At a splitting step it removes
the selected row. This is equivalent to the paper's rule once one shows
that previously tested rows are constant on subsequent candidate sets.
The paper's distinct-column assumption is NOT imposed on the deleted table.

Compilation status: NOT COMPILED (Lean/Mathlib absent in this runtime).
-/

noncomputable section

namespace GradientKey.P4

open Finset

variable {n m : ℕ}

/-- An arbitrary binary table; its columns need not be distinct. -/
abbrev Table (n m : ℕ) := Fin n → Fin m → Bool

/-- More generally, a binary table with an arbitrary finite row type. -/
abbrev RemainingTable (R : Type*) (m : ℕ) := R → Fin m → Bool

/-- Equal column vectors in a table, including all remaining rows. -/
def SameColumn {R : Type*} (B : RemainingTable R m)
    (a b : Fin m) : Prop := ∀ k, B k a = B k b

/-- Closure under the equality classes of a row-deleted table. -/
def PairClosed {R : Type*} (B : RemainingTable R m)
    (S : Finset (Fin m)) : Prop :=
  ∀ a b, a ∈ S → SameColumn B a b → b ∈ S

/-- Literal row deletion, with original indices retained as a subtype. -/
def deleteRow (A : Table n m) (r : Fin n) :
    RemainingTable {k : Fin n // k ≠ r} m :=
  fun k a => A k.1 a

/-- Count ones on a candidate set. -/
def ones (A : Table n m) (S : Finset (Fin m)) (r : Fin n) : ℕ :=
  (S.filter (fun a => A r a = true)).card

/-- Count zeros on a candidate set. -/
def zeros (A : Table n m) (S : Finset (Fin m)) (r : Fin n) : ℕ :=
  (S.filter (fun a => A r a = false)).card

/-- The paper's greedy row quality, `min(k,s-k)`. -/
def quality (A : Table n m) (S : Finset (Fin m)) (r : Fin n) : ℕ :=
  min (ones A S r) (zeros A S r)

/-- First maximum on a list. On tied scores it selects the earlier entry. -/
def firstMax {R : Type*} (q : R → ℕ) : List R → Option R
  | [] => none
  | a :: as =>
      match firstMax q as with
      | none => some a
      | some b => if q b ≤ q a then some a else some b

private theorem firstMax_cons_ne_none {R : Type*} (q : R → ℕ)
    (a : R) (xs : List R) : firstMax q (a :: xs) ≠ none := by
  simp only [firstMax]
  cases firstMax q xs <;> simp

private theorem firstMax_mem {R : Type*} (q : R → ℕ) :
    ∀ (xs : List R) (g : R), firstMax q xs = some g → g ∈ xs := by
  intro xs
  induction xs with
  | nil =>
      intro g hg
      simp [firstMax] at hg
  | cons a xs ih =>
      intro g hg
      cases ht : firstMax q xs with
      | none =>
          simp [firstMax, ht] at hg
          subst g
          simp
      | some b =>
          by_cases hba : q b ≤ q a
          · simp [firstMax, ht, hba] at hg
            subst g
            simp
          · simp [firstMax, ht, hba] at hg
            subst g
            exact List.mem_cons_of_mem _ (ih b ht)

private theorem firstMax_max {R : Type*} (q : R → ℕ) :
    ∀ (xs : List R) (g : R), firstMax q xs = some g →
      ∀ a ∈ xs, q a ≤ q g := by
  intro xs
  induction xs with
  | nil =>
      intro g hg a ha
      simp [firstMax] at hg
  | cons b xs ih =>
      intro g hg a ha
      cases ht : firstMax q xs with
      | none =>
          have hnil : xs = [] := by
            cases xs with
            | nil => rfl
            | cons x ys =>
                exact False.elim (firstMax_cons_ne_none q x ys ht)
          subst xs
          simp [firstMax] at hg
          subst g
          simp at ha
          subst a
          exact le_refl _
      | some c =>
          by_cases hcb : q c ≤ q b
          · simp [firstMax, ht, hcb] at hg
            subst g
            rcases List.mem_cons.mp ha with rfl | ha
            · exact le_refl _
            · exact (ih c ht a ha).trans hcb
          · simp [firstMax, ht, hcb] at hg
            subst g
            rcases List.mem_cons.mp ha with rfl | ha
            · omega
            · exact ih c ht a ha

/-- Removing a row other than the first maximizer preserves the winner.
This includes the first-in-original-order tie-breaking rule. -/
theorem firstMax_filter_not {R : Type*} [DecidableEq R]
    (q : R → ℕ) : ∀ (xs : List R) (r g : R),
      firstMax q xs = some g → g ≠ r →
        firstMax q (xs.filter (fun a => a ≠ r)) = some g := by
  intro xs
  induction xs with
  | nil =>
      intro r g hg hgr
      simp [firstMax] at hg
  | cons a xs ih =>
      intro r g hg hgr
      cases ht : firstMax q xs with
      | none =>
          have hnil : xs = [] := by
            cases xs with
            | nil => rfl
            | cons b ys =>
                exact False.elim (firstMax_cons_ne_none q b ys ht)
          subst xs
          simp [firstMax] at hg
          subst g
          simp [firstMax, hgr]
      | some b =>
          by_cases hba : q b ≤ q a
          · have hga : g = a := by
              simpa [firstMax, ht, hba] using hg.symm
            subst g
            cases hf : firstMax q (xs.filter (fun x => x ≠ r)) with
            | none =>
                simp [firstMax, hgr, hf]
            | some c =>
                have hc : c ∈ xs :=
                  (List.mem_filter.mp (firstMax_mem q _ c hf)).1
                have hca : q c ≤ q a :=
                  (firstMax_max q xs b ht c hc).trans hba
                simp [firstMax, hgr, hf, hca]
          · have hgb : g = b := by
              simpa [firstMax, ht, hba] using hg.symm
            subst g
            have hf : firstMax q (xs.filter (fun x => x ≠ r)) = some b :=
              ih r b ht hgr
            by_cases har : a = r
            · subst a
              simp [firstMax, hf]
            · simp [firstMax, har, hf, hba]

/-- The first maximum among currently available rows, with original order. -/
def selectRow (A : Table n m) (S : Finset (Fin m))
    (available : Finset (Fin n)) : Option (Fin n) :=
  firstMax (quality A S)
    ((List.finRange n).filter (fun r => r ∈ available))

private theorem selectRow_mem (A : Table n m) (S : Finset (Fin m))
    (available : Finset (Fin n)) (g : Fin n)
    (hg : selectRow A S available = some g) : g ∈ available := by
  exact (List.mem_filter.mp (firstMax_mem _ _ g hg)).2

private theorem list_filter_erase {R : Type*} [DecidableEq R]
    (xs : List R) (available : Finset R) (r : R) :
    xs.filter (fun x => x ∈ available.erase r) =
      (xs.filter (fun x => x ∈ available)).filter (fun x => x ≠ r) := by
  induction xs with
  | nil => rfl
  | cons a xs ih =>
      by_cases ha : a ∈ available <;> by_cases hr : a = r <;>
        simp [ha, hr, ih]

/-- The chosen row stays chosen if an unchosen row is deleted. -/
theorem selectRow_erase (A : Table n m) (S : Finset (Fin m))
    (available : Finset (Fin n)) (r g : Fin n)
    (hg : selectRow A S available = some g) (hgr : g ≠ r) :
    selectRow A S (available.erase r) = some g := by
  unfold selectRow at hg ⊢
  rw [list_filter_erase]
  exact firstMax_filter_not (quality A S) _ r g hg hgr

/-- State of a path; once stopped, both fields remain unchanged. -/
structure PathState (n m : ℕ) where
  candidate : Finset (Fin m)
  available : Finset (Fin n)
  deriving Inhabited

/-- One greedy fork, or identity if no remaining row splits the candidates. -/
def step (A : Table n m) (j : Fin m)
    (st : PathState n m) : PathState n m :=
  match selectRow A st.candidate st.available with
  | none => st
  | some g =>
      if 0 < quality A st.candidate g then
        { candidate := st.candidate.filter (fun a => A g a = A g j)
          available := st.available.erase g }
      else st

/-- Greedy path starting from a prescribed set of available rows. -/
def pathFrom (A : Table n m) (j : Fin m)
    (available : Finset (Fin n)) : ℕ → PathState n m
  | 0 => ⟨Finset.univ, available⟩
  | i + 1 => step A j (pathFrom A j available i)

/-- The ordinary full-table greedy path. -/
def fullState (A : Table n m) (j : Fin m) (i : ℕ) : PathState n m :=
  pathFrom A j Finset.univ i

/-- The path in the row-deleted table, still using original row numbers. -/
def deletedState (A : Table n m) (r : Fin n)
    (j : Fin m) (i : ℕ) : PathState n m :=
  pathFrom A j (Finset.univ.erase r) i

/-- `S_i^{(-r)}`, constant after termination, possibly of size > 1. -/
def deletedCandidate (A : Table n m) (r : Fin n)
    (j : Fin m) (i : ℕ) : Finset (Fin m) :=
  (deletedState A r j i).candidate

/-- A nonempty candidate set has a real-valued row split imbalance. -/
def rowImbalance (A : Table n m) (r : Fin n)
    (S : Finset (Fin m)) : ℝ :=
  (((S.card : ℝ) - 2 * (ones A S r : ℝ)) ^ 2) / (S.card : ℝ)

/-- The deleted-row imbalance variable used in Lemma 4.3. -/
def U (A : Table n m) (r : Fin n) (j : Fin m) (i : ℕ) : ℝ :=
  rowImbalance A r (deletedCandidate A r j i)

/-- An excluded row remains excluded at every subsequent step. -/
private theorem step_excluded (A : Table n m) (j : Fin m)
    (st : PathState n m) (r : Fin n) (hr : r ∉ st.available) :
    r ∉ (step A j st).available := by
  unfold step
  cases h : selectRow A st.candidate st.available with
  | none => simpa [h] using hr
  | some g =>
      by_cases hq : 0 < quality A st.candidate g
      · simp [h, hq, hr]
      · simpa [h, hq] using hr

private theorem step_contains (A : Table n m) (j : Fin m)
    (st : PathState n m) (hj : j ∈ st.candidate) :
    j ∈ (step A j st).candidate := by
  unfold step
  cases h : selectRow A st.candidate st.available with
  | none => simpa [h] using hj
  | some g =>
      by_cases hq : 0 < quality A st.candidate g
      · simp [h, hq, hj]
      · simpa [h, hq] using hj

/-- Even on a table with duplicate columns, the selected column survives. -/
theorem pathFrom_contains (A : Table n m) (j : Fin m)
    (available : Finset (Fin n)) (i : ℕ) :
    j ∈ (pathFrom A j available i).candidate := by
  induction i with
  | zero => simp [pathFrom]
  | succ i ih =>
      exact step_contains A j _ ih

/-- Consequently every deleted candidate set is nonempty. -/
theorem deletedCandidate_nonempty (A : Table n m) (r : Fin n)
    (j : Fin m) (i : ℕ) :
    0 < (deletedCandidate A r j i).card := by
  exact Finset.card_pos.mpr ⟨j, pathFrom_contains A j _ i⟩

private theorem pathFrom_excluded (A : Table n m) (r : Fin n)
    (j : Fin m) (i : ℕ) :
    r ∉ (deletedState A r j i).available := by
  induction i with
  | zero => simp [deletedState, pathFrom]
  | succ i ih =>
      exact step_excluded A j _ r ih

private theorem closed_step (A : Table n m) (r : Fin n)
    (j : Fin m) (st : PathState n m)
    (hexcluded : r ∉ st.available)
    (hclosed : PairClosed (deleteRow A r) st.candidate) :
    PairClosed (deleteRow A r) (step A j st).candidate := by
  unfold step
  cases h : selectRow A st.candidate st.available with
  | none => simpa [h] using hclosed
  | some g =>
      by_cases hq : 0 < quality A st.candidate g
      · change PairClosed (deleteRow A r)
          (st.candidate.filter (fun a => A g a = A g j))
        have hgr : g ≠ r := by
          intro he
          subst g
          exact hexcluded (selectRow_mem A st.candidate st.available r h)
        intro a b ha hab
        have haS : a ∈ st.candidate := (Finset.mem_filter.mp ha).1
        have haBit : A g a = A g j := (Finset.mem_filter.mp ha).2
        have hbS : b ∈ st.candidate := hclosed a b haS hab
        have hgb : A g a = A g b := hab ⟨g, hgr⟩
        exact Finset.mem_filter.mpr ⟨hbS, hgb.symm.trans haBit⟩
      · simpa [h, hq] using hclosed

/-- Every deleted candidate contains entire equality classes in `deleteRow`. -/
theorem deletedCandidate_pairClosed (A : Table n m) (r : Fin n)
    (j : Fin m) (i : ℕ) :
    PairClosed (deleteRow A r) (deletedCandidate A r j i) := by
  induction i with
  | zero =>
      intro a b ha hab
      simp [deletedCandidate, deletedState, pathFrom]
  | succ i ih =>
      exact closed_step A r j _ (pathFrom_excluded A r j i) ih

/-- Once a state has no splitting row, the step is the identity. -/
theorem step_stop (A : Table n m) (j : Fin m)
    (st : PathState n m)
    (h : ∀ g ∈ st.available, quality A st.candidate g = 0) :
    step A j st = st := by
  unfold step
  cases hg : selectRow A st.candidate st.available with
  | none => simp [hg]
  | some g =>
      have hz : quality A st.candidate g = 0 :=
        h g (selectRow_mem A st.candidate st.available g hg)
      simp [hg, hz]

/-- The terminal candidate set is unchanged at all later depths. -/
theorem pathFrom_constant_after_stop (A : Table n m) (j : Fin m)
    (available : Finset (Fin n)) (i k : ℕ)
    (h : ∀ g ∈ (pathFrom A j available i).available,
      quality A (pathFrom A j available i).candidate g = 0) :
    pathFrom A j available (i + k) = pathFrom A j available i := by
  induction k with
  | zero => simp
  | succ k ih =>
      rw [Nat.add_succ]
      change step A j (pathFrom A j available (i + k)) = _
      rw [ih]
      exact step_stop A j _ h

/-- One-step agreement when the full path chooses a row different from `r`. -/
theorem coupled_step (A : Table n m) (j : Fin m) (r g : Fin n)
    (full deleted : PathState n m)
    (hS : deleted.candidate = full.candidate)
    (hR : deleted.available = full.available.erase r)
    (hg : selectRow A full.candidate full.available = some g)
    (hgr : g ≠ r)
    (hq : 0 < quality A full.candidate g) :
    (step A j deleted).candidate = (step A j full).candidate ∧
    (step A j deleted).available = (step A j full).available.erase r := by
  have hd : selectRow A deleted.candidate deleted.available = some g := by
    rw [hS, hR]
    exact selectRow_erase A full.candidate full.available r g hg hgr
  constructor
  · simp [step, hg, hd, hq, hS]
  · simp [step, hg, hd, hq, hS, hR, Finset.erase_comm]

/-- Strong prefix hypothesis, discharged on the paper's event by P1:
all preceding full steps actually fork, and none selects the deleted row. -/
def PrefixAvoids (A : Table n m) (j : Fin m)
    (r : Fin n) (i : ℕ) : Prop :=
  ∀ d < i, ∃ g : Fin n,
    selectRow A (fullState A j d).candidate (fullState A j d).available = some g ∧
    0 < quality A (fullState A j d).candidate g ∧ g ≠ r

/-- Prefix coupling: agreement of candidate sets AND the remaining-row sets.
The row order is preserved by `selectRow_erase`, including ties. -/
theorem prefixCoupling (A : Table n m) (j : Fin m)
    (r : Fin n) (i : ℕ) (h : PrefixAvoids A j r i) :
    (deletedState A r j i).candidate = (fullState A j i).candidate ∧
    (deletedState A r j i).available =
      (fullState A j i).available.erase r := by
  induction i with
  | zero =>
      constructor <;> simp [deletedState, fullState, pathFrom]
  | succ i ih =>
      have hp : PrefixAvoids A j r i := by
        intro d hd
        exact h d (by omega)
      obtain ⟨hs, hr⟩ := ih hp
      obtain ⟨g, hg, hq, hgr⟩ := h i (by omega)
      exact coupled_step A j r g _ _ hs hr hg hgr hq

/-- The event-specific consequence needed by the mean and tail agents. -/
theorem imbalance_agrees (A : Table n m) (j : Fin m)
    (r : Fin n) (i : ℕ) (h : PrefixAvoids A j r i) :
    U A r j i = rowImbalance A r (fullState A j i).candidate := by
  rw [U, deletedCandidate, (prefixCoupling A j r i h).1]

/-- A full path's chosen row is maximal among available rows. -/
theorem selected_quality_max (A : Table n m)
    (S : Finset (Fin m)) (available : Finset (Fin n)) (g : Fin n)
    (hg : selectRow A S available = some g) :
    ∀ r ∈ available, quality A S r ≤ quality A S g := by
  intro r hr
  apply firstMax_max (quality A S) _ g hg r
  exact List.mem_filter.mpr ⟨List.mem_finRange r, hr⟩

/-- Number of available rows decreases by one at every splitting step.
This is the counting fact needed for `n-i` on a valid full path. -/
theorem step_available_card (A : Table n m) (j : Fin m)
    (st : PathState n m) (g : Fin n)
    (hg : selectRow A st.candidate st.available = some g)
    (hq : 0 < quality A st.candidate g) :
    (step A j st).available.card + 1 = st.available.card := by
  have hm : g ∈ st.available := selectRow_mem A st.candidate st.available g hg
  simp [step, hg, hq, Finset.card_erase_of_mem hm]

/-- If the full path splits at every level below `i`, precisely `n-i`
rows have not been tested. The valid-table fork-progress bridge is P1. -/
theorem full_unused_card (A : Table n m) (j : Fin m) (i : ℕ)
    (hForks : ∀ d < i, ∃ g : Fin n,
      selectRow A (fullState A j d).candidate (fullState A j d).available = some g ∧
      0 < quality A (fullState A j d).candidate g) :
    (fullState A j i).available.card + i = n := by
  induction i with
  | zero => simp [fullState, pathFrom]
  | succ i ih =>
      have hp : ∀ d < i, ∃ g : Fin n,
          selectRow A (fullState A j d).candidate (fullState A j d).available = some g ∧
          0 < quality A (fullState A j d).candidate g := by
        intro d hd
        exact hForks d (by omega)
      obtain ⟨g, hg, hq⟩ := hForks i (by omega)
      have hstep := step_available_card A j (fullState A j i) g hg hq
      have hprev := ih hp
      change (step A j (fullState A j i)).available.card + (i + 1) = n
      omega


/-- Available rows only decrease along the greedy path. -/
theorem step_available_subset (A : Table n m) (j : Fin m)
    (st : PathState n m) :
    (step A j st).available ⊆ st.available := by
  unfold step
  cases hg : selectRow A st.candidate st.available with
  | none => simp [hg]
  | some g =>
      by_cases hq : 0 < quality A st.candidate g
      · simpa [hg, hq] using (Finset.erase_subset g st.available)
      · simp [hg, hq]

/-- The paper's `E_r`: there is a fork at depth `i`, and the row has
not been used previously (equivalently, it remains available). -/
def Event (A : Table n m) (j : Fin m) (r : Fin n) (i : ℕ) : Prop :=
  2 ≤ (fullState A j i).candidate.card ∧
  r ∈ (fullState A j i).available

/-- If every preceding step forks, a row still available at level `i`
was not the selected row at any preceding step. -/
theorem prefixAvoids_of_available (A : Table n m) (j : Fin m)
    (r : Fin n) (i : ℕ)
    (hForks : ∀ d < i, ∃ g : Fin n,
      selectRow A (fullState A j d).candidate
        (fullState A j d).available = some g ∧
      0 < quality A (fullState A j d).candidate g)
    (hr : r ∈ (fullState A j i).available) :
    PrefixAvoids A j r i := by
  induction i with
  | zero =>
      intro d hd
      omega
  | succ i ih =>
      have hp : ∀ d < i, ∃ g : Fin n,
          selectRow A (fullState A j d).candidate
            (fullState A j d).available = some g ∧
          0 < quality A (fullState A j d).candidate g := by
        intro d hd
        exact hForks d (by omega)
      obtain ⟨g, hg, hq⟩ := hForks i (by omega)
      have hrPrev : r ∈ (fullState A j i).available :=
        step_available_subset A j (fullState A j i)
          (by simpa [fullState, pathFrom] using hr)
      have hprev := ih hp hrPrev
      intro d hd
      by_cases hdi : d < i
      · exact hprev d hdi
      · have hdeq : d = i := by omega
        subst d
        refine ⟨g, hg, hq, ?_⟩
        intro hgr
        subst g
        have hnot : r ∉ (step A j (fullState A j i)).available := by
          simp [step, hg, hq]
        exact hnot (by simpa [fullState, pathFrom] using hr)

/-- True event-based coupling, conditional only on the preceding
fork-progress property of the full greedy path (P1). -/
theorem event_prefixCoupling (A : Table n m) (j : Fin m)
    (r : Fin n) (i : ℕ)
    (hForks : ∀ d < i, ∃ g : Fin n,
      selectRow A (fullState A j d).candidate
        (fullState A j d).available = some g ∧
      0 < quality A (fullState A j d).candidate g)
    (he : Event A j r i) :
    deletedCandidate A r j i = (fullState A j i).candidate := by
  exact (prefixCoupling A j r i
    (prefixAvoids_of_available A j r i hForks he.2)).1

/-- The random variable `U_r` equals the full-row imbalance on `E_r`. -/
theorem U_on_event (A : Table n m) (j : Fin m)
    (r : Fin n) (i : ℕ)
    (hForks : ∀ d < i, ∃ g : Fin n,
      selectRow A (fullState A j d).candidate
        (fullState A j d).available = some g ∧
      0 < quality A (fullState A j d).candidate g)
    (he : Event A j r i) :
    U A r j i = rowImbalance A r (fullState A j i).candidate := by
  rw [U, event_prefixCoupling A j r i hForks he]

/-- The two bit values partition any candidate set. -/
theorem ones_add_zeros (A : Table n m) (S : Finset (Fin m))
    (r : Fin n) :
    ones A S r + zeros A S r = S.card := by
  classical
  induction S using Finset.induction_on with
  | empty => simp [ones, zeros]
  | @insert a S ha ih =>
      cases h : A r a <;>
        simp [ones, zeros, Finset.filter_insert, h, ha, ih]

private theorem twice_quality_le (A : Table n m)
    (S : Finset (Fin m)) (r : Fin n) :
    2 * quality A S r ≤ S.card := by
  have h := ones_add_zeros A S r
  have hl : quality A S r ≤ ones A S r := Nat.min_le_left _ _
  have hr : quality A S r ≤ zeros A S r := Nat.min_le_right _ _
  omega

/-- Exact identity between quality and squared split imbalance. -/
theorem rowImbalance_eq_quality (A : Table n m)
    (S : Finset (Fin m)) (r : Fin n) :
    rowImbalance A r S =
      (((S.card : ℝ) - 2 * (quality A S r : ℝ)) ^ 2) /
        (S.card : ℝ) := by
  have hc : ones A S r + zeros A S r = S.card :=
    ones_add_zeros A S r
  by_cases h : ones A S r ≤ zeros A S r
  · have hmin : quality A S r = ones A S r :=
      Nat.min_eq_left h
    simp only [rowImbalance, hmin]
  · have hmin : quality A S r = zeros A S r :=
      Nat.min_eq_right (by omega : zeros A S r ≤ ones A S r)
    have hcR : (S.card : ℝ) =
        (ones A S r : ℝ) + (zeros A S r : ℝ) := by
      exact_mod_cast hc.symm
    simp only [rowImbalance, hmin]
    congr 1
    rw [hcR]
    ring

/-- A row of greater greedy quality has no larger split imbalance. -/
theorem rowImbalance_antitone (A : Table n m)
    (S : Finset (Fin m)) (g r : Fin n)
    (h : quality A S r ≤ quality A S g) :
    rowImbalance A g S ≤ rowImbalance A r S := by
  rw [rowImbalance_eq_quality, rowImbalance_eq_quality]
  have hgr : (quality A S r : ℝ) ≤ (quality A S g : ℝ) := by
    exact_mod_cast h
  have hQg : 2 * (quality A S g : ℝ) ≤ (S.card : ℝ) := by
    exact_mod_cast twice_quality_le A S g
  have hQr : 2 * (quality A S r : ℝ) ≤ (S.card : ℝ) := by
    exact_mod_cast twice_quality_le A S r
  let x : ℝ := (S.card : ℝ) - 2 * (quality A S g : ℝ)
  let y : ℝ := (S.card : ℝ) - 2 * (quality A S r : ℝ)
  have hx : 0 ≤ x := by dsimp [x]; linarith
  have hy : 0 ≤ y := by dsimp [y]; linarith
  have hxy : x ≤ y := by dsimp [x, y]; linarith
  have hprod : 0 ≤ (y - x) * (y + x) :=
    mul_nonneg (sub_nonneg.mpr hxy) (add_nonneg hy hx)
  have hsq : x ^ 2 ≤ y ^ 2 := by nlinarith
  exact div_le_div_of_nonneg_right hsq (Nat.cast_nonneg _)

/-- At a fork the full greedy row is the best available row. -/
def actualImbalance (A : Table n m) (j : Fin m) (i : ℕ) : ℝ :=
  let st := fullState A j i
  if 2 ≤ st.candidate.card then
    match selectRow A st.candidate st.available with
    | some g => rowImbalance A g st.candidate
    | none => 0
  else 0

/-- Split imbalance is always nonnegative. -/
theorem rowImbalance_nonneg (A : Table n m) (r : Fin n)
    (S : Finset (Fin m)) : 0 ≤ rowImbalance A r S := by
  unfold rowImbalance
  positivity

/-- Deterministic mean comparison over the actual unused rows.
P1 supplies the preceding fork and current-fork properties from
validity of the full table and `s_i ≥ 2`. -/
theorem actualImbalance_le_unused_mean (A : Table n m) (j : Fin m)
    (i : ℕ) (hi : i < n)
    (hForks : ∀ d < i, ∃ g : Fin n,
      selectRow A (fullState A j d).candidate
        (fullState A j d).available = some g ∧
      0 < quality A (fullState A j d).candidate g)
    (hCurrent : 2 ≤ (fullState A j i).candidate.card →
      ∃ g : Fin n,
        selectRow A (fullState A j i).candidate
          (fullState A j i).available = some g ∧
        0 < quality A (fullState A j i).candidate g) :
    actualImbalance A j i ≤
      (∑ r ∈ (fullState A j i).available,
        rowImbalance A r (fullState A j i).candidate) /
          ((n : ℝ) - (i : ℝ)) := by
  let st := fullState A j i
  have hcard := full_unused_card A j i hForks
  have hcardR : (st.available.card : ℝ) = (n : ℝ) - (i : ℝ) := by
    change (st.available.card : ℝ) = _
    have hr : (st.available.card : ℝ) + (i : ℝ) = (n : ℝ) := by
      exact_mod_cast hcard
    linarith
  have hd : (0 : ℝ) < (n : ℝ) - (i : ℝ) := by
    have hiR : (i : ℝ) < (n : ℝ) := by exact_mod_cast hi
    linarith
  by_cases hf : 2 ≤ st.candidate.card
  · obtain ⟨g, hg, hq⟩ := hCurrent hf
    have hmin : ∀ r ∈ st.available,
        rowImbalance A g st.candidate ≤ rowImbalance A r st.candidate := by
      intro r hr
      exact rowImbalance_antitone A st.candidate g r
        (selected_quality_max A st.candidate st.available g hg r hr)
    have hsum :
        (∑ _r ∈ st.available, rowImbalance A g st.candidate) ≤
        (∑ r ∈ st.available, rowImbalance A r st.candidate) := by
      exact Finset.sum_le_sum (fun r hr => hmin r hr)
    have hmul :
        actualImbalance A j i * ((n : ℝ) - (i : ℝ)) ≤
          (∑ r ∈ st.available, rowImbalance A r st.candidate) := by
      calc
        actualImbalance A j i * ((n : ℝ) - (i : ℝ)) =
            ∑ _r ∈ st.available, rowImbalance A g st.candidate := by
              simp [actualImbalance, st, hf, hg, hcardR, mul_comm]
        _ ≤ _ := hsum
    exact (le_div_iff₀ hd).2 hmul
  · have hz : actualImbalance A j i = 0 := by
      simp [actualImbalance, st, hf]
    rw [hz]
    exact div_nonneg
      (Finset.sum_nonneg (fun r _ => rowImbalance_nonneg A r st.candidate))
      hd.le

/-- Convert the available-row sum into the event sum used in Lemma 4.3. -/
theorem event_sum_eq_unused_sum (A : Table n m) (j : Fin m)
    (i : ℕ)
    (hForks : ∀ d < i, ∃ g : Fin n,
      selectRow A (fullState A j d).candidate
        (fullState A j d).available = some g ∧
      0 < quality A (fullState A j d).candidate g)
    (hf : 2 ≤ (fullState A j i).candidate.card) :
    (∑ r : Fin n, if Event A j r i then U A r j i else 0) =
      ∑ r ∈ (fullState A j i).available,
        rowImbalance A r (fullState A j i).candidate := by
  classical
  have hterm : ∀ r : Fin n,
      (if Event A j r i then U A r j i else 0) =
        if r ∈ (fullState A j i).available then
          rowImbalance A r (fullState A j i).candidate else 0 := by
    intro r
    by_cases hr : r ∈ (fullState A j i).available
    · have he : Event A j r i := ⟨hf, hr⟩
      simp [he, hr, U_on_event A j r i hForks he]
    · have he : ¬ Event A j r i := fun e => hr e.2
      simp [he, hr]
  simp_rw [hterm]
  rw [← Finset.sum_filter]
  simp

/-- Exact pointwise comparison in Lemma 4.3, with the single remaining
P1 dependency made explicit in `hForks` and `hCurrent`. -/
theorem pointwise_greedy_comparison (A : Table n m) (j : Fin m)
    (i : ℕ) (hi : i < n)
    (hForks : ∀ d < i, ∃ g : Fin n,
      selectRow A (fullState A j d).candidate
        (fullState A j d).available = some g ∧
      0 < quality A (fullState A j d).candidate g)
    (hCurrent : 2 ≤ (fullState A j i).candidate.card →
      ∃ g : Fin n,
        selectRow A (fullState A j i).candidate
          (fullState A j i).available = some g ∧
        0 < quality A (fullState A j i).candidate g) :
    actualImbalance A j i ≤
      (∑ r : Fin n, if Event A j r i then U A r j i else 0) /
        ((n : ℝ) - (i : ℝ)) := by
  have hbase := actualImbalance_le_unused_mean A j i hi hForks hCurrent
  by_cases hf : 2 ≤ (fullState A j i).candidate.card
  · rw [event_sum_eq_unused_sum A j i hForks hf]
    exact hbase
  · have hzero : actualImbalance A j i = 0 := by
      simp [actualImbalance, hf]
    rw [hzero]
    have hnonneg : 0 ≤
        ∑ r : Fin n, if Event A j r i then U A r j i else 0 := by
      apply Finset.sum_nonneg
      intro r _
      split_ifs
      · exact rowImbalance_nonneg A r (deletedCandidate A r j i)
      · exact le_refl 0
    exact div_nonneg hnonneg (by
      have hiR : (i : ℝ) < (n : ℝ) := by exact_mod_cast hi
      linarith)

end GradientKey.P4
