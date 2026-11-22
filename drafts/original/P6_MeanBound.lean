import GradientKeySection4

/-!
# P6 — the mean part of Lemma 4.3

This is an *integration module*, not an unconditional proof of Lemma 4.3.
It imports the uncompiled v4 baseline and explicitly isolates interfaces
which P1, P3 and P4 must discharge.  In particular:

* P3 supplies `fibreEquiv` and its compatibility with deleted-row data;
* P1 supplies `unusedCount`, and P4 supplies `greedyLower`;
* no additional probability or second-moment hypothesis is postulated.

No `sorry`, `admit`, `axiom`, or `unsafe` is used. NOT COMPILED.
-/

noncomputable section

namespace GradientKey.P6

open Finset
open GradientKey.Concrete
open GradientKey.RowDeletion

variable {k m : ℕ}

/-- Physically delete row `r`, renumbering the others in increasing order.
The ambient table has `k+1` rows, so zero-row deletions work too. -/
def deleteRow (A : Concrete.Table (k + 1) m) (r : Fin (k + 1)) :
    RowDeletion.RemainingTable k m :=
  fun t a => A (r.succAbove t) a

/-- The row returned by the same first-in-row-order greedy rule, possibly
absent when the remaining table has zero rows. -/
noncomputable def deletedChoice (B : RowDeletion.RemainingTable k m)
    (S : Finset (Fin m)) : Option (Fin k) :=
  List.argmax (Concrete.quality B S) (List.finRange k)

/-- Unlike the valid-table recursion, a deleted-row tree can have a
non-singleton leaf if all its remaining rows are constant there. -/
noncomputable def deletedStep (B : RowDeletion.RemainingTable k m)
    (S : Finset (Fin m)) (j : Fin m) : Finset (Fin m) :=
  if S.card ≤ 1 then S else
    match deletedChoice B S with
    | none => S
    | some g =>
      if Concrete.quality B S g = 0 then S
      else S.filter (fun a => B g a = B g j)

/-- Candidate set in the row-deleted greedy tree. It is kept constant
once no remaining row splits it, even if it contains duplicate columns. -/
noncomputable def deletedCandidateAt
    (B : RowDeletion.RemainingTable k m) (j : Fin m) :
    ℕ → Finset (Fin m)
  | 0 => Finset.univ
  | i + 1 => deletedStep B (deletedCandidateAt B j i) j

/-- The selected column remains present after each deleted-tree step. -/
theorem deletedStep_mem (B : RowDeletion.RemainingTable k m)
    (S : Finset (Fin m)) (j : Fin m) (hj : j ∈ S) :
    j ∈ deletedStep B S j := by
  classical
  unfold deletedStep
  by_cases hsmall : S.card ≤ 1
  · simp [hsmall, hj]
  · simp only [hsmall, ↓reduceIte]
    cases hchoice : deletedChoice B S with
    | none => simpa [hchoice] using hj
    | some g =>
        by_cases hzero : Concrete.quality B S g = 0
        · simpa [hchoice, hzero] using hj
        · simp [hchoice, hzero, hj]

theorem deletedCandidate_mem (B : RowDeletion.RemainingTable k m)
    (j : Fin m) (i : ℕ) : j ∈ deletedCandidateAt B j i := by
  classical
  induction i with
  | zero => simp [deletedCandidateAt]
  | succ i ih =>
      change j ∈ deletedStep B (deletedCandidateAt B j i) j
      exact deletedStep_mem B _ j ih

theorem deletedCandidate_nonempty (B : RowDeletion.RemainingTable k m)
    (j : Fin m) (i : ℕ) : 0 < (deletedCandidateAt B j i).card := by
  exact Finset.card_pos.mpr ⟨j, deletedCandidate_mem B j i⟩

/-- A filter by one of B's rows cannot separate B-identical columns. -/
theorem deletedStep_pairClosed (B : RowDeletion.RemainingTable k m)
    (S : Finset (Fin m)) (j : Fin m)
    (hS : RowDeletion.PairClosed B S) :
    RowDeletion.PairClosed B (deletedStep B S j) := by
  classical
  intro a b ha hab
  unfold deletedStep at ha ⊢
  by_cases hsmall : S.card ≤ 1
  · simpa [hsmall] using hS a b (by simpa [hsmall] using ha) hab
  · cases hchoice : deletedChoice B S with
    | none => simpa [hsmall, hchoice] using
          hS a b (by simpa [hsmall, hchoice] using ha) hab
    | some g =>
        by_cases hzero : Concrete.quality B S g = 0
        · simpa [hsmall, hchoice, hzero] using
            hS a b (by simpa [hsmall, hchoice, hzero] using ha) hab
        · have ha' : a ∈ S ∧ B g a = B g j := by
            simpa [hsmall, hchoice, hzero] using ha
          have hb' : b ∈ S ∧ B g b = B g j :=
            ⟨hS a b ha'.1 hab, (hab g).symm.trans ha'.2⟩
          simpa [hsmall, hchoice, hzero] using
            (Finset.mem_filter.mpr hb')

/-- Every deleted-tree candidate set contains whole B-equality classes. -/
theorem deletedCandidate_pairClosed (B : RowDeletion.RemainingTable k m)
    (j : Fin m) (i : ℕ) :
    RowDeletion.PairClosed B (deletedCandidateAt B j i) := by
  classical
  induction i with
  | zero =>
      intro a b _ _
      simp [deletedCandidateAt]
  | succ i ih =>
      change RowDeletion.PairClosed B
        (deletedStep B (deletedCandidateAt B j i) j)
      exact deletedStep_pairClosed B _ j ih

/-- The event that row r was tested strictly above depth i. -/
def testedBefore (hn : 0 < k + 1)
    (r : Fin (k + 1)) (ω : Concrete.Sample (k + 1) m)
    (i : ℕ) : Prop :=
  ∃ d : ℕ, d < i ∧
    2 ≤ (Concrete.candidateAt ω.1.1 ω.2 hn d).card ∧
    Concrete.greedyRow ω.1.1
      (Concrete.candidateAt ω.1.1 ω.2 hn d) hn = r

/-- Event E_r of Lemma 4.3. -/
def active (hn : 0 < k + 1)
    (r : Fin (k + 1)) (ω : Concrete.Sample (k + 1) m)
    (i : ℕ) : Prop :=
  2 ≤ Concrete.sampleSize hn ω i ∧ ¬testedBefore hn r ω i

/-- The row-deleted candidate set S_i^(-r). -/
noncomputable def rowDeletedCandidate
    (r : Fin (k + 1)) (ω : Concrete.Sample (k + 1) m)
    (i : ℕ) : Finset (Fin m) :=
  deletedCandidateAt (deleteRow ω.1.1 r) ω.2 i

/-- U_r = v_r(S_i^(-r)). -/
noncomputable def U (r : Fin (k + 1))
    (i : ℕ) (ω : Concrete.Sample (k + 1) m) : ℝ :=
  RowDeletion.insertedImbalance (fun a => ω.1.1 r a)
    (rowDeletedCandidate r ω i)

/-- Actual split imbalance v_i. -/
noncomputable def actual (hn : 0 < k + 1)
    (i : ℕ) (ω : Concrete.Sample (k + 1) m) : ℝ :=
  Concrete.sampleImbalance hn ω i

/-- Finite uniform mean. This is definitionally equal to the v4
baseline's (private) `GradientKey.finiteAverage`. -/
noncomputable def sampleAverage (f : Concrete.Sample (k + 1) m → ℝ) : ℝ :=
  (∑ ω : Concrete.Sample (k + 1) m, f ω) /
    (Fintype.card (Concrete.Sample (k + 1) m) : ℝ)

/-- Expected v_i in the concrete uniform sample space. -/
noncomputable def V (hn : 0 < k + 1) (i : ℕ) : ℝ :=
  sampleAverage (actual hn i)

/-- U_r is pointwise nonnegative even when m=0. -/
theorem U_nonneg (r : Fin (k + 1)) (i : ℕ)
    (ω : Concrete.Sample (k + 1) m) : 0 ≤ U r i ω := by
  unfold U RowDeletion.insertedImbalance
  exact div_nonneg (sq_nonneg _) (Nat.cast_nonneg _)

/-!
## P3: transport of uniform sampling to finite deleted-row fibres

For each r, deleting r is a bijection between valid full tables and
pairs (B, admissible inserted row). The column j is unchanged. P3 is
responsible for constructing this equivalence and showing it transports
`U` to the function below. The `fibreEquiv`/`hTransport` arguments are
**interfaces, not proved facts**.
-/

abbrev Fibres (k m : ℕ) :=
  (Σ B : RowDeletion.RemainingTable k m, RowDeletion.Extension B) × Fin m

noncomputable def fibreU (i : ℕ) (y : Fibres k m) : ℝ :=
  RowDeletion.insertedImbalance y.1.2.1
    (deletedCandidateAt y.1.1 y.2 i)

/-- A fixed B,j fibre has total inserted imbalance at most its size.
The empty-extension case contributes 0. No *assumed* moment bound. -/
theorem fibre_sum_le_card (B : RowDeletion.RemainingTable k m)
    (j : Fin m) (i : ℕ) :
    (∑ x : RowDeletion.Extension B,
       RowDeletion.insertedImbalance x.1 (deletedCandidateAt B j i)) ≤
       (Fintype.card (RowDeletion.Extension B) : ℝ) := by
  classical
  by_cases hex : Nonempty (RowDeletion.Extension B)
  · letI : Nonempty (RowDeletion.Extension B) := hex
    have hMean := RowDeletion.conditional_inserted_imbalance_le_one
      B (deletedCandidateAt B j i)
      (deletedCandidate_nonempty B j i)
      (deletedCandidate_pairClosed B j i)
    change
      (∑ x : RowDeletion.Extension B,
        RowDeletion.insertedImbalance x.1 (deletedCandidateAt B j i)) /
        (Fintype.card (RowDeletion.Extension B) : ℝ) ≤ 1 at hMean
    have hc : (0 : ℝ) < Fintype.card (RowDeletion.Extension B) := by
      exact_mod_cast (Fintype.card_pos : 0 <
        Fintype.card (RowDeletion.Extension B))
    exact (div_le_one hc).mp hMean
  · letI : IsEmpty (RowDeletion.Extension B) :=
      ⟨fun x => hex ⟨x⟩⟩
    simp

/-- The finite fibre-law step of P3, with a precise equivalence and
transport equation as its only dependencies. It includes averaging over
all B and j, including empty fibres, and proves E[U_r] ≤ 1. -/
theorem row_mean_le_one_of_P3
    [Nonempty (Concrete.Sample (k + 1) m)]
    (r : Fin (k + 1)) (i : ℕ)
    (e : Concrete.Sample (k + 1) m ≃ Fibres k m)
    (hTransport : ∀ ω : Concrete.Sample (k + 1) m,
      U r i ω = fibreU i (e ω)) :
    sampleAverage (U r i) ≤ 1 := by
  classical
  have hfibre :
      (∑ y : Fibres k m, fibreU i y) ≤
      (∑ y : Fibres k m, (1 : ℝ)) := by
    -- Sum first by remaining table B, then by column j, then by inserted row.
    simp only [Fintype.sum_prod_type, Fintype.sum_sigma]
    apply Finset.sum_le_sum
    intro B _
    calc
      (∑ x : RowDeletion.Extension B, ∑ j : Fin m,
          fibreU i (⟨B, x⟩, j)) =
        (∑ j : Fin m, ∑ x : RowDeletion.Extension B,
          fibreU i (⟨B, x⟩, j)) := Finset.sum_comm
      _ ≤ ∑ j : Fin m, ∑ x : RowDeletion.Extension B, (1 : ℝ) := by
        apply Finset.sum_le_sum
        intro j _
        simpa [fibreU] using fibre_sum_le_card B j i
      _ = ∑ x : RowDeletion.Extension B, ∑ j : Fin m, (1 : ℝ) :=
        Finset.sum_comm
  have hsum :
      (∑ ω : Concrete.Sample (k + 1) m, U r i ω) ≤
      (∑ ω : Concrete.Sample (k + 1) m, (1 : ℝ)) := by
    have htransportSum :
        (∑ ω : Concrete.Sample (k + 1) m, U r i ω) =
        (∑ y : Fibres k m, fibreU i y) := by
      calc
        _ = ∑ ω : Concrete.Sample (k + 1) m, fibreU i (e ω) :=
          Finset.sum_congr rfl (fun ω _ => hTransport ω)
        _ = ∑ y : Fibres k m, fibreU i y := Equiv.sum_comp e _
    have hconstSum :
        (∑ y : Fibres k m, (1 : ℝ)) =
        (∑ ω : Concrete.Sample (k + 1) m, (1 : ℝ)) := by
      simpa using (Equiv.sum_comp e (fun _ : Fibres k m => (1 : ℝ))).symm
    calc
      _ = ∑ y : Fibres k m, fibreU i y := htransportSum
      _ ≤ ∑ y : Fibres k m, (1 : ℝ) := hfibre
      _ = ∑ ω : Concrete.Sample (k + 1) m, (1 : ℝ) := hconstSum
  have hc : (0 : ℝ) < Fintype.card (Concrete.Sample (k + 1) m) := by
    exact_mod_cast (Fintype.card_pos : 0 <
      Fintype.card (Concrete.Sample (k + 1) m))
  change
    (∑ ω : Concrete.Sample (k + 1) m, U r i ω) /
       (Fintype.card (Concrete.Sample (k + 1) m) : ℝ) ≤ 1
  apply (div_le_one hc).mpr
  simpa using hsum

/-!
## P1/P4: exact number of active rows and greedy comparison

P1 will supply the exact count of the active rows at a fork; P4 will
supply pointwise U_r ≥ v_i for those rows (via deleted-path agreement).
The following averaging proof is P6's contribution and does not assume
row independence.
-/

theorem pointwise_greedy_average_of_P1_P4
    (hn : 0 < k + 1) (i : ℕ) (hi : i < k + 1)
    (unusedCount : ∀ ω : Concrete.Sample (k + 1) m,
      2 ≤ Concrete.sampleSize hn ω i →
      (∑ r : Fin (k + 1), if active hn r ω i then (1 : ℝ) else 0) =
         ((k + 1 : ℕ) : ℝ) - (i : ℝ))
    (greedyLower : ∀ (ω : Concrete.Sample (k + 1) m)
      (r : Fin (k + 1)), active hn r ω i →
        actual hn i ω ≤ U r i ω) :
    ∀ ω : Concrete.Sample (k + 1) m,
      actual hn i ω ≤
        (∑ r : Fin (k + 1), if active hn r ω i then U r i ω else 0) /
          (((k + 1 : ℕ) : ℝ) - (i : ℝ)) := by
  classical
  intro ω
  have hiR : (i : ℝ) < ((k + 1 : ℕ) : ℝ) := by exact_mod_cast hi
  have hd : 0 < ((k + 1 : ℕ) : ℝ) - (i : ℝ) := by linarith
  by_cases hfork : 2 ≤ Concrete.sampleSize hn ω i
  · have hTerm : ∀ r : Fin (k + 1),
        (if active hn r ω i then actual hn i ω else 0) ≤
          (if active hn r ω i then U r i ω else 0) := by
      intro r
      split_ifs with hr
      · exact greedyLower ω r hr
      · exact le_refl _
    have hWeighted :
        (∑ r : Fin (k + 1), if active hn r ω i then actual hn i ω else 0) =
          actual hn i ω *
            (∑ r : Fin (k + 1), if active hn r ω i then (1 : ℝ) else 0) := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro r _
      split_ifs <;> ring
    have hsum :
        actual hn i ω * (((k + 1 : ℕ) : ℝ) - (i : ℝ)) ≤
          (∑ r : Fin (k + 1), if active hn r ω i then U r i ω else 0) := by
      rw [← unusedCount ω hfork, ← hWeighted]
      apply Finset.sum_le_sum
      intro r _
      exact hTerm r
    exact (le_div_iff₀ hd).mpr hsum
  · have hz : actual hn i ω = 0 :=
      Concrete.sampleImbalance_zero_leaf hn ω i (Nat.lt_of_not_ge hfork)
    have hnone : ∀ r : Fin (k + 1), ¬ active hn r ω i :=
      fun _ hr => hfork hr.1
    simp [hz, hnone]

/-- CONDITIONAL INTEGRATION THEOREM, NOT THE UNCONDITIONAL LEMMA 4.3.
P1/P4 must establish `unusedCount` and `greedyLower`; P3 must establish
the row-deletion equivalences and transport equations below. -/
theorem expectedImbalance_le_rows_of_P1_P3_P4
    [Nonempty (Concrete.Sample (k + 1) m)]
    (hn : 0 < k + 1) (i : ℕ) (hi : i < k + 1)
    (unusedCount : ∀ ω : Concrete.Sample (k + 1) m,
      2 ≤ Concrete.sampleSize hn ω i →
      (∑ r : Fin (k + 1), if active hn r ω i then (1 : ℝ) else 0) =
        ((k + 1 : ℕ) : ℝ) - (i : ℝ))
    (greedyLower : ∀ (ω : Concrete.Sample (k + 1) m)
      (r : Fin (k + 1)), active hn r ω i →
        actual hn i ω ≤ U r i ω)
    (fibreEquiv : ∀ r : Fin (k + 1),
      Concrete.Sample (k + 1) m ≃ Fibres k m)
    (fibreTransport : ∀ (r : Fin (k + 1))
      (ω : Concrete.Sample (k + 1) m),
        U r i ω = fibreU i (fibreEquiv r ω)) :
    V hn i ≤ ((k + 1 : ℕ) : ℝ) /
      (((k + 1 : ℕ) : ℝ) - (i : ℝ)) := by
  have hPoint := pointwise_greedy_average_of_P1_P4 hn i hi
    unusedCount greedyLower
  have hRow : ∀ r : Fin (k + 1), sampleAverage (U r i) ≤ 1 := by
    intro r
    exact row_mean_le_one_of_P3 r i (fibreEquiv r)
      (fibreTransport r)
  have hResult := GradientKey.mean_imbalance_from_unused_rows
    (Ω := Concrete.Sample (k + 1) m)
    (k + 1) i hi (actual hn i) (fun r ω => U r i ω)
    (fun r ω => active hn r ω i)
    (fun r ω => U_nonneg r i ω) hPoint
    (by
      intro r
      change sampleAverage (U r i) ≤ 1
      exact hRow r)
  change V hn i ≤ ((k + 1 : ℕ) : ℝ) /
      (((k + 1 : ℕ) : ℝ) - (i : ℝ))
  exact hResult

end GradientKey.P6
