import DeletedPath
import Hoeffding
import Truncation
import Lemma41

/-!
# Lemma 4.3 for the concrete greedy path

Rows are `Fin (n+1)`.  For a row `r` and depth `i`:
* `Evt A hn j i r` is the event `E_r`: `s_i ≥ 2` and `G(A)` does not test `r`
  at depths `0, …, i-1` of the path of `j`;
* `Urow i r ω = v_r(S_i^{(-r)})`, the split imbalance of row `r` on the
  candidate set of the deleted path.

Proved: the greedy comparison `(n+1-i) v_i ≤ ∑_r 1_{E_r} U_r` (pointwise),
`E U_r ≤ 1` and `|{U_r > z}| ≤ 2 e^{-z/2} N` (via P3's fibres, Lemma 4.2 and
the Hoeffding module), and the two bounds of Lemma 4.3.
-/

noncomputable section

namespace GradientKey.Concrete

open Finset

variable {n m : ℕ}

/-! ## Split imbalance of a row -/

/-- `v_r(S) = (s-2k)^2/s`. -/
def rowImb {k : ℕ} (A : Table k m) (S : Finset (Fin m)) (r : Fin k) : ℝ :=
  RowDeletion.insertedImbalance (A r) S

theorem rowImb_nonneg {k : ℕ} (A : Table k m) (S : Finset (Fin m)) (r : Fin k) :
    0 ≤ rowImb A S r :=
  div_nonneg (sq_nonneg _) (Nat.cast_nonneg _)

theorem ones_add_zeros {k : ℕ} (A : Table k m) (S : Finset (Fin m)) (r : Fin k) :
    ones A S r + zeros A S r = S.card := by
  have h := Finset.card_filter_add_card_filter_not (s := S) (fun a => A r a = true)
  simpa [ones, zeros] using h

theorem rowImb_eq_quality {k : ℕ} (A : Table k m) (S : Finset (Fin m)) (r : Fin k) :
    rowImb A S r = ((S.card : ℝ) - 2 * (quality A S r : ℝ)) ^ 2 / (S.card : ℝ) := by
  unfold rowImb RowDeletion.insertedImbalance
  have hs := ones_add_zeros A S r
  change ((S.card : ℝ) - 2 * (ones A S r : ℝ)) ^ 2 / _ = _
  congr 1
  unfold quality
  rcases le_total (ones A S r) (zeros A S r) with h | h
  · rw [min_eq_left h]
  · rw [min_eq_right h]
    have hsR : (S.card : ℝ) = (ones A S r : ℝ) + (zeros A S r : ℝ) := by exact_mod_cast hs.symm
    rw [hsR]; ring

/-- The row of `G` has the least split imbalance. -/
theorem rowImb_greedy_le {k : ℕ} (A : Table k m) (S : Finset (Fin m)) (hk : 0 < k)
    (r : Fin k) : rowImb A S (greedyRow A S hk) ≤ rowImb A S r := by
  rw [rowImb_eq_quality, rowImb_eq_quality]
  apply div_le_div_of_nonneg_right _ (Nat.cast_nonneg _)
  have hq := p1_greedy_quality_max A S hk r
  have hqR : (quality A S r : ℝ) ≤ (quality A S (greedyRow A S hk) : ℝ) := by exact_mod_cast hq
  have hhalf : ∀ t, 2 * (quality A S t : ℝ) ≤ S.card := by
    intro t
    have hs := ones_add_zeros A S t
    have : 2 * quality A S t ≤ S.card := by unfold quality; omega
    exact_mod_cast this
  have h0 := hhalf (greedyRow A S hk)
  exact pow_le_pow_left₀ (by linarith) (by linarith) 2

theorem localImbalance_eq_rowImb {k : ℕ} (A : Table k m) (S : Finset (Fin m)) (hk : 0 < k)
    (h : 2 ≤ S.card) : localImbalance A S hk = rowImb A S (greedyRow A S hk) := by
  unfold localImbalance
  rw [if_neg (by omega)]
  rfl

/-! ## The event `E_r` and the number of untested rows -/

/-- `E_r`: a fork at depth `i`, and `r` not tested at depths `< i`. -/
def Evt (A : Table (n + 1) m) (hn : 0 < n + 1) (j : Fin m) (i : ℕ) (r : Fin (n + 1)) :
    Prop :=
  2 ≤ (candidateAt A j hn i).card ∧ ∀ d < i, greedyRow A (candidateAt A j hn d) hn ≠ r

instance (A : Table (n + 1) m) (hn : 0 < n + 1) (j : Fin m) (i : ℕ) (r : Fin (n + 1)) :
    Decidable (Evt A hn j i r) := by
  unfold Evt; infer_instance

/-- The rows tested at depths `< i`. -/
def tested (A : Table (n + 1) m) (hn : 0 < n + 1) (j : Fin m) (i : ℕ) : Finset (Fin (n + 1)) :=
  (Finset.range i).image (fun d => greedyRow A (candidateAt A j hn d) hn)

theorem card_tested (A : Table (n + 1) m) (hA : DistinctColumns A) (hn : 0 < n + 1)
    (j : Fin m) (i : ℕ) (h : 2 ≤ (candidateAt A j hn i).card) :
    (tested A hn j i).card = i := by
  unfold tested
  have hfork : ∀ t < i, 2 ≤ (candidateAt A j hn t).card := fun t ht =>
    le_trans h (Finset.card_le_card (p1_candidate_subset_of_le A j hn ht.le))
  rw [Finset.card_image_of_injOn, Finset.card_range]
  intro d hd d' hd' heq
  have hd : d < i := Finset.mem_range.mp hd
  have hd' : d' < i := Finset.mem_range.mp hd'
  by_contra hne
  rcases lt_or_gt_of_ne hne with hlt | hlt
  · exact p1_no_row_reuse A hA j hn hlt (hfork d' hd') heq
  · exact p1_no_row_reuse A hA j hn hlt (hfork d hd) heq.symm

/-- On a fork at depth `i`, exactly `n + 1 - i` rows are untested. -/
theorem card_evt (A : Table (n + 1) m) (hA : DistinctColumns A) (hn : 0 < n + 1)
    (j : Fin m) (i : ℕ) :
    (Finset.univ.filter (Evt A hn j i)).card =
      if 2 ≤ (candidateAt A j hn i).card then n + 1 - i else 0 := by
  split_ifs with h
  · have hset : Finset.univ.filter (Evt A hn j i) = Finset.univ \ tested A hn j i := by
      ext r
      simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_sdiff, Evt, tested,
        Finset.mem_image, Finset.mem_range, not_exists, not_and]
      exact ⟨fun h' d hd => h'.2 d hd, fun h' => ⟨h, h'⟩⟩
    rw [hset, Finset.card_univ_diff, card_tested A hA hn j i h, Fintype.card_fin]
  · rw [Finset.card_eq_zero, Finset.filter_eq_empty_iff]
    intro r _ hr
    exact h hr.1

/-- Pointwise greedy comparison: `(n+1-i) v_i ≤ ∑_r 1_{E_r} v_r(S_i^{(-r)})`. -/
theorem pointwise_comparison (A : Table (n + 1) m) (hA : DistinctColumns A) (hn : 0 < n + 1)
    (j : Fin m) (i : ℕ) :
    ((n + 1 - i : ℕ) : ℝ) * localImbalance A (candidateAt A j hn i) hn ≤
      ∑ r : Fin (n + 1),
        if Evt A hn j i r then rowImb A (delCand A r j i) r else 0 := by
  by_cases h : 2 ≤ (candidateAt A j hn i).card
  · rw [← Finset.sum_filter]
    have hcard := card_evt A hA hn j i
    rw [if_pos h] at hcard
    have hle : ∀ r ∈ Finset.univ.filter (Evt A hn j i),
        localImbalance A (candidateAt A j hn i) hn ≤ rowImb A (delCand A r j i) r := by
      intro r hr
      have hE := (Finset.mem_filter.mp hr).2
      rw [delCand_eq_candidateAt A hA hn r j i hE.1 hE.2 i le_rfl,
        localImbalance_eq_rowImb A _ hn h]
      exact rowImb_greedy_le A _ hn r
    have hsum := Finset.card_nsmul_le_sum _ _ _ hle
    rw [hcard, nsmul_eq_mul] at hsum
    exact hsum
  · unfold localImbalance
    rw [if_pos (by omega), mul_zero]
    apply Finset.sum_nonneg
    intro r _
    split_ifs
    · exact rowImb_nonneg _ _ _
    · exact le_refl 0

/-! ## The deleted-row variables on the sample space -/

theorem delCand_mem (A : Table (n + 1) m) (r : Fin (n + 1)) (j : Fin m) (i : ℕ) :
    j ∈ delCand A r j i := by
  induction i with
  | zero => exact Finset.mem_univ j
  | succ i ih =>
      change j ∈ delStep A r (delCand A r j i) j
      unfold delStep
      cases delRow A r (delCand A r j i) with
      | none => exact ih
      | some g =>
          simp only
          split_ifs
          · exact Finset.mem_filter.mpr ⟨ih, rfl⟩
          · exact ih

/-- `S_i^{(-r)}` as a function of the deleted table `∂_r A` and the column. -/
def candOfDeleted (r : Fin (n + 1)) (i : ℕ) (B : RowDeletion.RemainingTable n m)
    (j : Fin m) : Finset (Fin m) :=
  delCand (P3.insertRow B r (fun _ => false)) r j i

theorem candOfDeleted_deleteRow (r : Fin (n + 1)) (i : ℕ) (A : Table (n + 1) m) (j : Fin m) :
    candOfDeleted r i (P3.deleteRow A r) j = delCand A r j i := by
  unfold candOfDeleted
  apply delCand_congr
  intro k hk
  obtain ⟨k', rfl⟩ := Fin.exists_succAbove_eq hk
  rw [P3.insertRow_other]
  rfl

theorem candOfDeleted_good (r : Fin (n + 1)) (i : ℕ) (B : RowDeletion.RemainingTable n m)
    (j : Fin m) :
    0 < (candOfDeleted r i B j).card ∧ RowDeletion.PairClosed B (candOfDeleted r i B j) := by
  refine ⟨Finset.card_pos.mpr ⟨j, delCand_mem _ r j i⟩, ?_⟩
  have h := delCand_pairClosed (P3.insertRow B r (fun _ => false)) r j i
  rw [P3.deleteRow_insertRow] at h
  exact h

/-- `U_r = v_r(S_i^{(-r)})` on the sample space. -/
def Urow (hn : 0 < n + 1) (i : ℕ) (r : Fin (n + 1)) (ω : Sample (n + 1) m) : ℝ :=
  rowImb ω.1.1 (delCand ω.1.1 r ω.2 i) r

theorem sampleU_eq (hn : 0 < n + 1) (i : ℕ) (r : Fin (n + 1)) (ω : Sample (n + 1) m) :
    P3.sampleU r (candOfDeleted r i) ω = Urow hn i r ω := by
  unfold P3.sampleU Urow rowImb
  rw [candOfDeleted_deleteRow]

/-- `E U_r ≤ 1` (Lemma 4.2, averaged over the deletion fibres). -/
theorem Urow_mean_le_one [Nonempty (Sample (n + 1) m)] (hn : 0 < n + 1) (i : ℕ)
    (r : Fin (n + 1)) :
    (∑ ω : Sample (n + 1) m, Urow hn i r ω) ≤ (Fintype.card (Sample (n + 1) m) : ℝ) := by
  have h := P3.unconditional_row_mean_le_one (m := m) r (candOfDeleted r i)
    (fun B j₀ _ => candOfDeleted_good r i B j₀)
  unfold P3.uniformMean at h
  have hpos : (0 : ℝ) < Fintype.card (Sample (n + 1) m) := by
    exact_mod_cast Fintype.card_pos
  rw [div_le_iff₀ hpos, one_mul] at h
  simpa only [sampleU_eq hn i r] using h

/-- `|{U_r > z}| ≤ 2 e^{-z/2} N` (Lemma 4.2, averaged over the deletion fibres). -/
theorem Urow_tail [Nonempty (Sample (n + 1) m)] (hn : 0 < n + 1) (i : ℕ)
    (r : Fin (n + 1)) (z : ℝ) (hz : 0 < z) :
    ((Finset.univ.filter (fun ω : Sample (n + 1) m => z < Urow hn i r ω)).card : ℝ) ≤
      2 * Real.exp (-z / 2) * (Fintype.card (Sample (n + 1) m) : ℝ) := by
  have h := P3.unconditional_row_tail_of_extension_tails (m := m) r (candOfDeleted r i) z
    (2 * Real.exp (-z / 2)) (by
      intro B j₀ hpos
      obtain ⟨hS, hcl⟩ := candOfDeleted_good r i B j₀
      have hE := RowDeletion.conditional_inserted_imbalance_tail B _ hS hcl z hz
      have hposR : (0 : ℝ) < Fintype.card (RowDeletion.Extension B) := by exact_mod_cast hpos
      rw [Finset.sum_boole, div_le_iff₀ hposR]
      exact hE)
  unfold P3.uniformMean at h
  have hpos : (0 : ℝ) < Fintype.card (Sample (n + 1) m) := by
    exact_mod_cast Fintype.card_pos
  rw [Finset.sum_boole, div_le_iff₀ hpos] at h
  simpa only [sampleU_eq hn i r] using h

/-! ## Lemma 4.3 -/

/-- The fork event on the sample. -/
def forkSet (hn : 0 < n + 1) (i : ℕ) : Finset (Sample (n + 1) m) :=
  Finset.univ.filter (fun ω => 2 ≤ sampleSize hn ω i)

/-- The event `E_r` on the sample. -/
def evtSet (hn : 0 < n + 1) (i : ℕ) (r : Fin (n + 1)) : Finset (Sample (n + 1) m) :=
  Finset.univ.filter (fun ω => Evt ω.1.1 hn ω.2 i r)

/-- Summed greedy comparison. -/
theorem summed_comparison (hn : 0 < n + 1) (i : ℕ) :
    ((n + 1 - i : ℕ) : ℝ) * (∑ ω : Sample (n + 1) m, sampleImbalance hn ω i) ≤
      ∑ r : Fin (n + 1), ∑ ω ∈ evtSet (m := m) hn i r, Urow hn i r ω := by
  rw [Finset.mul_sum]
  calc (∑ ω : Sample (n + 1) m, ((n + 1 - i : ℕ) : ℝ) * sampleImbalance hn ω i)
      ≤ ∑ ω : Sample (n + 1) m, ∑ r : Fin (n + 1),
          if Evt ω.1.1 hn ω.2 i r then Urow hn i r ω else 0 :=
        Finset.sum_le_sum (fun ω _ => pointwise_comparison ω.1.1 ω.1.2 hn ω.2 i)
    _ = ∑ r : Fin (n + 1), ∑ ω ∈ evtSet (m := m) hn i r, Urow hn i r ω := by
        rw [Finset.sum_comm]
        apply Finset.sum_congr rfl
        intro r _
        rw [evtSet, Finset.sum_filter]

/-- `∑_r |E_r| = (n+1-i) |{s_i ≥ 2}|`. -/
theorem sum_card_evtSet (hn : 0 < n + 1) (i : ℕ) :
    (∑ r : Fin (n + 1), ((evtSet (m := m) hn i r).card : ℝ)) =
      ((n + 1 - i : ℕ) : ℝ) * ((forkSet (m := m) hn i).card : ℝ) := by
  have h1 : ∀ r : Fin (n + 1), ((evtSet (m := m) hn i r).card : ℝ) =
      ∑ ω : Sample (n + 1) m, if Evt ω.1.1 hn ω.2 i r then (1 : ℝ) else 0 := by
    intro r
    rw [Finset.sum_boole]
    rfl
  simp only [h1]
  rw [Finset.sum_comm]
  have h2 : ∀ ω : Sample (n + 1) m,
      (∑ r : Fin (n + 1), if Evt ω.1.1 hn ω.2 i r then (1 : ℝ) else 0) =
        if 2 ≤ sampleSize hn ω i then ((n + 1 - i : ℕ) : ℝ) else 0 := by
    intro ω
    rw [Finset.sum_boole, card_evt ω.1.1 ω.1.2 hn ω.2 i]
    unfold sampleSize
    split_ifs <;> simp
  simp only [h2]
  rw [← Finset.sum_filter, Finset.sum_const, nsmul_eq_mul, mul_comm]
  rfl

variable [Nonempty (Sample (n + 1) m)]

/-- **Lemma 4.3, first bound**: `V_i ≤ n/(n-i)` (here with `n+1` rows). -/
theorem expectedImbalance_le_rows (hn : 0 < n + 1) (i : ℕ) (hi : i < n + 1) :
    (p1_finitePathData (m := m) hn).expectedImbalance i ≤
      ((n + 1 : ℕ) : ℝ) / (((n + 1 : ℕ) : ℝ) - (i : ℝ)) := by
  have hN : (0 : ℝ) < Fintype.card (Sample (n + 1) m) := by exact_mod_cast Fintype.card_pos
  have hd : (0 : ℝ) < ((n + 1 - i : ℕ) : ℝ) := by
    exact_mod_cast Nat.sub_pos_of_lt hi
  have hcast : ((n + 1 - i : ℕ) : ℝ) = ((n + 1 : ℕ) : ℝ) - (i : ℝ) := by
    rw [Nat.cast_sub hi.le]
  have hsum := summed_comparison (m := m) hn i
  have hrows : (∑ r : Fin (n + 1), ∑ ω ∈ evtSet (m := m) hn i r, Urow hn i r ω) ≤
      ((n + 1 : ℕ) : ℝ) * (Fintype.card (Sample (n + 1) m) : ℝ) := by
    calc (∑ r : Fin (n + 1), ∑ ω ∈ evtSet (m := m) hn i r, Urow hn i r ω)
        ≤ ∑ r : Fin (n + 1), ∑ ω : Sample (n + 1) m, Urow hn i r ω := by
          apply Finset.sum_le_sum
          intro r _
          exact Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset _ _)
            (fun ω _ _ => rowImb_nonneg _ _ _)
      _ ≤ ∑ _r : Fin (n + 1), (Fintype.card (Sample (n + 1) m) : ℝ) :=
          Finset.sum_le_sum (fun r _ => Urow_mean_le_one hn i r)
      _ = ((n + 1 : ℕ) : ℝ) * (Fintype.card (Sample (n + 1) m) : ℝ) := by
          rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
  unfold FinitePathData.expectedImbalance finiteAverage
  change (∑ ω : Sample (n + 1) m, sampleImbalance hn ω i) / _ ≤ _
  rw [← hcast, div_le_div_iff₀ hN hd]
  nlinarith [hsum, hrows]

/-- **Lemma 4.3, second bound**:
`V_i ≤ 2 p_i (1 + ln (2n/((n-i) p_i)))` for `p_i > 0` (here with `n+1` rows). -/
theorem expectedImbalance_le_log (hn : 0 < n + 1) (i : ℕ) (hi : i < n + 1)
    (hp : 0 < (p1_finitePathData (m := m) hn).forkProb i) :
    (p1_finitePathData (m := m) hn).expectedImbalance i ≤
      2 * (p1_finitePathData (m := m) hn).forkProb i * (1 + Real.log
        (2 * ((n + 1 : ℕ) : ℝ) /
          ((((n + 1 : ℕ) : ℝ) - (i : ℝ)) * (p1_finitePathData (m := m) hn).forkProb i))) := by
  set N : ℝ := (Fintype.card (Sample (n + 1) m) : ℝ)
  have hN : (0 : ℝ) < N := by simp only [N]; exact_mod_cast Fintype.card_pos
  have hcast : ((n + 1 - i : ℕ) : ℝ) = ((n + 1 : ℕ) : ℝ) - (i : ℝ) := by
    rw [Nat.cast_sub hi.le]
  have hforkProb : (p1_finitePathData (m := m) hn).forkProb i =
      ((forkSet (m := m) hn i).card : ℝ) / N := by
    unfold FinitePathData.forkProb finiteAverage
    rw [Finset.sum_boole]
    rfl
  have hV : (p1_finitePathData (m := m) hn).expectedImbalance i =
      (∑ ω : Sample (n + 1) m, sampleImbalance hn ω i) / N := rfl
  have h := P7.tailAggregation_of_truncated (n := n + 1) (i := i) hi
    (fun r => ((evtSet (m := m) hn i r).card : ℝ) / N)
    (fun r => (∑ ω ∈ evtSet (m := m) hn i r, Urow hn i r ω) / N)
    ((p1_finitePathData (m := m) hn).forkProb i)
    ((p1_finitePathData (m := m) hn).expectedImbalance i)
    (fun r => div_nonneg (Nat.cast_nonneg _) hN.le) hp
    (by
      rw [← Finset.sum_div, sum_card_evtSet, hforkProb, mul_div_assoc])
    (by
      intro r
      have ht := Truncation.sum_on_event_le_phi (Urow hn i r)
        (fun ω => rowImb_nonneg _ _ _) (evtSet hn i r) (fun z hz => Urow_tail (m := m) hn i r z hz)
      rw [div_le_iff₀ hN, mul_comm]
      exact ht)
    (by
      rw [hV, ← Finset.sum_div, mul_div_assoc']
      exact div_le_div_of_nonneg_right (summed_comparison hn i) hN.le)
  rw [hcast] at h
  exact h

end GradientKey.Concrete
