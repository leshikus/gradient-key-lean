import P1_GreedyPath
import P3_ConditionalFibre

/-!
# The greedy path of a row-deleted table

For a table `A` with rows `Fin (n+1)` and a row `r`, the path of `j` in
`G(∂_r A)` uses only the rows `k ≠ r`, in their original order.  At a
candidate set `S` it takes the first row `g ≠ r` of largest quality; if that
quality is `0` (no remaining row splits `S`) the path stays at `S`, which may
hold several equal columns.  This is the rule of Section 4 for tables whose
columns need not be distinct.

Proved here:
* `delCand_congr`: the deleted path depends only on the rows `k ≠ r`;
* `delCand_pairClosed`: its candidate sets are closed under equal columns of
  `∂_r A` (in the `Fin.removeNth` representation used by P3);
* `delCand_eq_candidateAt`: if the full path has a fork at depth `i` and did
  not test `r` at depths `< i`, the two paths agree up to depth `i`.
-/

noncomputable section

namespace GradientKey.Concrete

open Finset

/-! ## Two facts about `List.argmax` -/

theorem argmax_congr {α β : Type*} [LinearOrder β] (f g : α → β) :
    ∀ l : List α, (∀ a ∈ l, f a = g a) → List.argmax f l = List.argmax g l
  | [], _ => rfl
  | a :: t, h => by
      rw [List.argmax_cons, List.argmax_cons,
        argmax_congr f g t (fun b hb => h b (List.mem_cons_of_mem _ hb))]
      cases hc : List.argmax g t with
      | none => rfl
      | some c =>
          have hct : c ∈ t := List.argmax_mem hc
          simp only [h a List.mem_cons_self, h c (List.mem_cons_of_mem _ hct)]

/-- Deleting entries other than the first maximizer keeps the first maximizer. -/
theorem argmax_filter {α β : Type*} [LinearOrder β] (f : α → β) (p : α → Bool) :
    ∀ (l : List α) (g : α), List.argmax f l = some g → p g = true →
      List.argmax f (l.filter p) = some g
  | [], g, h, _ => by simp at h
  | a :: t, g, h, hp => by
      rw [List.argmax_cons] at h
      cases hc : List.argmax f t with
      | none =>
          rw [hc] at h
          have ht : t = [] := List.argmax_eq_none.mp hc
          subst ht
          simp only [Option.some.injEq] at h
          subst h
          simp [List.filter, hp]
      | some c =>
          rw [hc] at h
          simp only at h
          by_cases hac : f a < f c
          · rw [if_pos hac] at h
            simp only [Option.some.injEq] at h
            subst h
            have ih := argmax_filter f p t c hc hp
            rw [List.filter_cons]
            by_cases hpa : p a = true
            · rw [if_pos hpa, List.argmax_cons, ih]
              simp [hac]
            · rw [if_neg hpa]; exact ih
          · rw [if_neg hac] at h
            simp only [Option.some.injEq] at h
            subst h
            rw [List.filter_cons, if_pos hp, List.argmax_cons]
            cases hc' : List.argmax f (t.filter p) with
            | none => rfl
            | some c' =>
                have hc't : c' ∈ t := (List.mem_filter.mp (List.argmax_mem hc')).1
                have hle : f c' ≤ f c := List.le_of_mem_argmax hc't hc
                have hnot : ¬ f a < f c' := by
                  intro hlt; exact hac (lt_of_lt_of_le hlt hle)
                simp [hnot]

variable {n m : ℕ}

/-! ## The deleted-row greedy path -/

/-- The first row `≠ r` of largest quality on `S` (none if `n = 0`). -/
def delRow (A : Table (n + 1) m) (r : Fin (n + 1)) (S : Finset (Fin m)) :
    Option (Fin (n + 1)) :=
  List.argmax (quality A S) ((List.finRange (n + 1)).filter (fun k => decide (k ≠ r)))

/-- One step of `G(∂_r A)` on the path of `j`. -/
def delStep (A : Table (n + 1) m) (r : Fin (n + 1)) (S : Finset (Fin m))
    (j : Fin m) : Finset (Fin m) :=
  match delRow A r S with
  | none => S
  | some g => if 0 < quality A S g then S.filter (fun k => A g k = A g j) else S

/-- `S_i^{(-r)}`: candidate set at depth `i` on the path of `j` in `G(∂_r A)`,
constant once the path has ended. -/
def delCand (A : Table (n + 1) m) (r : Fin (n + 1)) (j : Fin m) : ℕ → Finset (Fin m)
  | 0 => Finset.univ
  | i + 1 => delStep A r (delCand A r j i) j

theorem delRow_ne {A : Table (n + 1) m} {r : Fin (n + 1)} {S : Finset (Fin m)}
    {g : Fin (n + 1)} (h : delRow A r S = some g) : g ≠ r := by
  have hm := List.argmax_mem h
  simpa using (List.mem_filter.mp hm).2

theorem quality_congr {A A' : Table (n + 1) m} {k : Fin (n + 1)}
    (h : A k = A' k) (S : Finset (Fin m)) : quality A S k = quality A' S k := by
  simp only [quality, ones, zeros, h]

/-- The deleted path depends only on the rows other than `r`. -/
theorem delCand_congr {A A' : Table (n + 1) m} {r : Fin (n + 1)}
    (h : ∀ k, k ≠ r → A k = A' k) (j : Fin m) (i : ℕ) :
    delCand A r j i = delCand A' r j i := by
  induction i with
  | zero => rfl
  | succ i ih =>
      change delStep A r (delCand A r j i) j = delStep A' r (delCand A' r j i) j
      rw [ih]
      set S := delCand A' r j i
      have hrow : delRow A r S = delRow A' r S := by
        unfold delRow
        apply argmax_congr
        intro k hk
        have hkr : k ≠ r := by simpa using (List.mem_filter.mp hk).2
        exact quality_congr (h k hkr) S
      unfold delStep
      rw [hrow]
      cases hg : delRow A' r S with
      | none => rfl
      | some g =>
          have hgr := delRow_ne hg
          simp only [quality_congr (h g hgr) S, h g hgr]

/-- The candidate sets of `G(∂_r A)` contain both or none of each pair of
equal columns of `∂_r A`. -/
theorem delCand_pairClosed (A : Table (n + 1) m) (r : Fin (n + 1)) (j : Fin m) (i : ℕ) :
    RowDeletion.PairClosed (P3.deleteRow A r) (delCand A r j i) := by
  induction i with
  | zero => intro a b _ _; exact Finset.mem_univ b
  | succ i ih =>
      change RowDeletion.PairClosed (P3.deleteRow A r) (delStep A r (delCand A r j i) j)
      unfold delStep
      cases hg : delRow A r (delCand A r j i) with
      | none => exact ih
      | some g =>
          simp only
          split_ifs with hq
          · intro a b ha hab
            have haS := (Finset.mem_filter.mp ha).1
            have haB := (Finset.mem_filter.mp ha).2
            obtain ⟨k, hk⟩ := Fin.exists_succAbove_eq (delRow_ne hg)
            have hgab : A g a = A g b := by
              have := hab k
              simp only [P3.deleteRow, Fin.removeNth, hk] at this
              exact this
            exact Finset.mem_filter.mpr ⟨ih a b haS hab, hgab.symm.trans haB⟩
          · exact ih

/-- **Prefix coupling.** If the full path has a fork at depth `i` and does not
test `r` at the depths `0, …, i-1`, then `S_d^{(-r)} = S_d` for `d ≤ i`. -/
theorem delCand_eq_candidateAt (A : Table (n + 1) m) (hA : DistinctColumns A)
    (hn : 0 < n + 1) (r : Fin (n + 1)) (j : Fin m) (i : ℕ)
    (hfork : 2 ≤ (candidateAt A j hn i).card)
    (hr : ∀ d < i, greedyRow A (candidateAt A j hn d) hn ≠ r) :
    ∀ d ≤ i, delCand A r j d = candidateAt A j hn d := by
  intro d hd
  induction d with
  | zero => rfl
  | succ d ih =>
      have hdi : d < i := hd
      change delStep A r (delCand A r j d) j = candidateStep A (candidateAt A j hn d) j hn
      rw [ih hdi.le]
      set S := candidateAt A j hn d
      have hS : 2 ≤ S.card :=
        le_trans hfork (Finset.card_le_card (p1_candidate_subset_of_le A j hn hdi.le))
      set g := greedyRow A S hn
      have hrow : delRow A r S = some g := by
        unfold delRow
        apply argmax_filter
        · exact p1_argmax_some A S hn
        · simpa using hr d hdi
      have hq : 0 < quality A S g :=
        p1_greedy_quality_pos A hA S j hn (p1_candidate_mem A j hn d) hS
      unfold delStep candidateStep
      rw [hrow]
      simp only [if_pos hq, if_neg (show ¬ S.card ≤ 1 by omega)]
      rfl

end GradientKey.Concrete
