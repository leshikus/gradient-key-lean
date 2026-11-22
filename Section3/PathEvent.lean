import PathRows

/-!
# Proposition 3.1: the rowwise conditions are exactly the greedy path

For candidate sets `S₀,…,S_d` with `S₀ = univ` and `|S_j| ≥ 2` for `j < d`, and an injective schedule
`ρ : Fin d ↪ Fin n`, `fixedPathRowwise S j₀ ρ A` holds iff the path of column `j₀` in `G(A)` has
candidate sets `S₀,…,S_d` and tests row `ρ j` at depth `j`. On a table with distinct columns the
schedule exists and is unique, so the indicator of the path is the number of admissible schedules.
-/

noncomputable section

namespace GradientKey.Concrete

open Finset Classical

variable {n m d : ℕ}

theorem quality_eq_rq (A : Table n m) (S : Finset (Fin m)) (r : Fin n) :
    quality A S r = rq S (A r) := rfl

/-- The quality of a row is the smaller side of the split it induces. -/
theorem rq_split (S : Finset (Fin m)) (row : Row m) (j₀ : Fin m) :
    rq S row = min ((S \ S.filter (fun k => row k = row j₀)).card)
      (S.filter (fun k => row k = row j₀)).card := by
  rw [← Finset.filter_not]
  unfold rq
  cases h : row j₀
  · rw [show S.filter (fun k => row k = true) = S.filter (fun k => ¬ row k = false) from
      Finset.filter_congr (fun k _ => by cases row k <;> simp)]
  · rw [show S.filter (fun k => row k = false) = S.filter (fun k => ¬ row k = true) from
      Finset.filter_congr (fun k _ => by cases row k <;> simp)]
    omega

/-- The selected row at depth `j` has quality `q_j`. -/
theorem quality_selected (A : Table n m) (S : Fin (d + 1) → Finset (Fin m)) (j₀ : Fin m)
    (j : Fin d) (r : Fin n)
    (hsplit : S j.succ = (S j.castSucc).filter (fun k => A r k = A r j₀)) :
    quality A (S j.castSucc) r = fixedPathQuality S j := by
  rw [quality_eq_rq, rq_split _ _ j₀, fixedPathQuality, hsplit]

/-- Under the rowwise conditions, the greedy row at `S_j` is `ρ j`. -/
theorem greedyRow_of_rowwise (A : Table n m) (hn : 0 < n)
    (S : Fin (d + 1) → Finset (Fin m)) (j₀ : Fin m) (rho : Fin d ↪ Fin n)
    (h : fixedPathRowwise S j₀ rho A) (j : Fin d) :
    greedyRow A (S j.castSucc) hn = rho j := by
  have hq := quality_selected A S j₀ j (rho j) ((h (rho j) j).1 rfl)
  have hcond : ∀ t : Fin n, t ≠ rho j →
      (if t < rho j then quality A (S j.castSucc) t < fixedPathQuality S j
       else quality A (S j.castSucc) t ≤ fixedPathQuality S j) :=
    fun t ht => (h t j).2 (Ne.symm ht)
  apply greedyRow_eq_of_quality_order
  · intro t
    by_cases ht : t = rho j
    · rw [ht]
    · have := hcond t ht
      rw [hq]
      split_ifs at this
      · exact this.le
      · exact this
  · intro t ht
    have := hcond t (ne_of_lt ht)
    rw [if_pos ht] at this
    rw [hq]; exact this

/-- Under the rowwise conditions, the candidate sets of `j₀` are `S₀,…,S_d`. -/
theorem candidateAt_of_rowwise (A : Table n m) (hn : 0 < n)
    (S : Fin (d + 1) → Finset (Fin m)) (j₀ : Fin m) (rho : Fin d ↪ Fin n)
    (h0 : S 0 = univ) (h2 : ∀ j : Fin d, 2 ≤ (S j.castSucc).card)
    (h : fixedPathRowwise S j₀ rho A) (i : Fin (d + 1)) :
    candidateAt A j₀ hn i = S i := by
  induction i using Fin.induction with
  | zero => rw [h0]; rfl
  | succ j ih =>
    have hc : candidateAt A j₀ hn (j.succ : ℕ) =
        candidateStep A (candidateAt A j₀ hn (j.castSucc : ℕ)) j₀ hn := rfl
    rw [hc, ih]
    unfold candidateStep
    rw [if_neg (by have := h2 j; omega), greedyRow_of_rowwise A hn S j₀ rho h j]
    exact ((h (rho j) j).1 rfl).symm

/-- On a table with distinct columns, the path determines an admissible schedule: the greedy rows. -/
theorem rowwise_of_candidateAt (A : Table n m) (hA : DistinctColumns A) (hn : 0 < n)
    (S : Fin (d + 1) → Finset (Fin m)) (j₀ : Fin m)
    (h2 : ∀ j : Fin d, 2 ≤ (S j.castSucc).card)
    (hS : ∀ i : Fin (d + 1), candidateAt A j₀ hn i = S i) :
    ∃ rho : Fin d ↪ Fin n, (∀ j, rho j = greedyRow A (S j.castSucc) hn) ∧
      fixedPathRowwise S j₀ rho A := by
  have hcs : ∀ j : Fin d, candidateAt A j₀ hn j = S j.castSucc := fun j => hS j.castSucc
  have hsucc : ∀ j : Fin d, S j.succ = candidateStep A (S j.castSucc) j₀ hn := by
    intro j
    rw [← hS j.succ, ← hcs j]
    rfl
  have hinj : Function.Injective (fun j : Fin d => greedyRow A (S j.castSucc) hn) := by
    have key : ∀ a b : Fin d, (a : ℕ) < b →
        greedyRow A (S a.castSucc) hn ≠ greedyRow A (S b.castSucc) hn := by
      intro a b hab
      rw [← hcs a, ← hcs b]
      exact p1_no_row_reuse A hA j₀ hn hab (by rw [hcs b]; exact h2 b)
    intro a b hab
    by_contra hne
    rcases lt_or_gt_of_ne (Fin.val_ne_of_ne hne) with hlt | hlt
    · exact key a b hlt hab
    · exact key b a hlt hab.symm
  refine ⟨⟨_, hinj⟩, fun j => rfl, ?_⟩
  intro i j
  have hstep : pathOneStepTest A (S j.castSucc) (S j.succ) j₀ (greedyRow A (S j.castSucc) hn) :=
    (pathOneStepTest_iff A _ _ j₀ hn _ (h2 j)).mpr ⟨rfl, (hsucc j).symm⟩
  obtain ⟨hT, hbefore, hafter⟩ := hstep
  have hq := quality_selected A S j₀ j _ hT
  constructor
  · intro hi
    change greedyRow A (S j.castSucc) hn = i at hi
    rw [← hi]; exact hT
  · intro hi
    change greedyRow A (S j.castSucc) hn ≠ i at hi
    change (if i < greedyRow A (S j.castSucc) hn then
        quality A (S j.castSucc) i < fixedPathQuality S j
      else quality A (S j.castSucc) i ≤ fixedPathQuality S j)
    rw [← hq]
    split_ifs with hlt
    · exact hbefore i hlt
    · exact hafter i (lt_of_le_of_ne (not_lt.mp hlt) hi)

/-- The schedule is unique: it is the list of greedy rows. -/
theorem rowwise_unique (A : Table n m) (hn : 0 < n)
    (S : Fin (d + 1) → Finset (Fin m)) (j₀ : Fin m) (rho rho' : Fin d ↪ Fin n)
    (h : fixedPathRowwise S j₀ rho A) (h' : fixedPathRowwise S j₀ rho' A) : rho = rho' := by
  ext j
  rw [← greedyRow_of_rowwise A hn S j₀ rho h j, ← greedyRow_of_rowwise A hn S j₀ rho' h' j]

/-- On a table with distinct columns, the indicator of the path is the number of admissible
schedules. -/
theorem path_indicator_eq_sum (A : Table n m) (hA : DistinctColumns A) (hn : 0 < n)
    (S : Fin (d + 1) → Finset (Fin m)) (j₀ : Fin m)
    (h0 : S 0 = univ) (h2 : ∀ j : Fin d, 2 ≤ (S j.castSucc).card) :
    (if ∀ i : Fin (d + 1), candidateAt A j₀ hn i = S i then (1 : ℤ) else 0) =
      ∑ rho : Fin d ↪ Fin n, if fixedPathRowwise S j₀ rho A then (1 : ℤ) else 0 := by
  by_cases hp : ∀ i : Fin (d + 1), candidateAt A j₀ hn i = S i
  · obtain ⟨rho, -, hrho⟩ := rowwise_of_candidateAt A hA hn S j₀ h2 hp
    rw [if_pos hp, Finset.sum_eq_single rho]
    · rw [if_pos hrho]
    · intro rho' _ hne
      rw [if_neg]
      intro h'
      exact hne (rowwise_unique A hn S j₀ rho' rho h' hrho)
    · intro h; exact absurd (mem_univ rho) h
  · rw [if_neg hp]
    symm
    apply Finset.sum_eq_zero
    intro rho _
    rw [if_neg]
    intro h
    exact hp (candidateAt_of_rowwise A hn S j₀ rho h0 h2 h)

/-- Counting valid tables by a property of the underlying table. -/
theorem card_valid_filter (P : Table n m → Prop) :
    ((univ.filter (fun A : ValidTable n m => P A.1)).card : ℤ) =
      ∑ A : Table n m, if P A ∧ DistinctColumns A then (1 : ℤ) else 0 := by
  rw [Finset.sum_boole]
  congr 1
  rw [← Fintype.card_subtype, ← Fintype.card_subtype]
  exact Fintype.card_congr ((Equiv.subtypeSubtypeEquivSubtypeInter
    (fun A : Table n m => DistinctColumns A) P).trans
    (Equiv.subtypeEquivRight (fun _ => and_comm)))

/-- **Path count.** The number of valid tables whose column `j₀` has candidate sets `S₀,…,S_d` is
a sum over schedules of Möbius-weighted products of row counts. -/
theorem card_path_eq (hn : 0 < n) (S : Fin (d + 1) → Finset (Fin m)) (j₀ : Fin m)
    (h0 : S 0 = univ) (h2 : ∀ j : Fin d, 2 ≤ (S j.castSucc).card) :
    ((univ.filter (fun A : ValidTable n m =>
        ∀ i : Fin (d + 1), candidateAt A.1 j₀ hn i = S i)).card : ℤ) =
      ∑ rho : Fin d ↪ Fin n, ∑ c : OrderedFinpartition m,
        mu c * ∏ i : Fin n,
          ((univ.filter (fun row : Row m =>
            fixedPathRowAdmissible S j₀ rho i row ∧ ConstOn c row)).card : ℤ) := by
  have hv := card_valid_filter (n := n) (m := m)
    (fun A => ∀ i : Fin (d + 1), candidateAt A j₀ hn i = S i)
  beta_reduce at hv
  refine Eq.trans (b := ∑ A : Table n m,
    if (∀ i : Fin (d + 1), candidateAt A j₀ hn i = S i) ∧ DistinctColumns A then (1 : ℤ) else 0)
    (by convert hv using 3; congr 1) ?_
  have hpt : ∀ A : Table n m,
      (if (∀ i : Fin (d + 1), candidateAt A j₀ hn i = S i) ∧ DistinctColumns A then (1 : ℤ) else 0) =
        ∑ rho : Fin d ↪ Fin n,
          if fixedPathRowwise S j₀ rho A ∧ DistinctColumns A then (1 : ℤ) else 0 := by
    intro A
    by_cases hA : DistinctColumns A
    · simp only [and_iff_left hA]
      exact path_indicator_eq_sum A hA hn S j₀ h0 h2
    · simp [hA]
  rw [Finset.sum_congr rfl (fun A _ => hpt A), Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro rho _
  exact fixedPath_mobius_factor S j₀ rho

end GradientKey.Concrete
