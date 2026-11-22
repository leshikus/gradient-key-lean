import NearBall

/-!
# `k + 2` missing words (second case of Proposition 3.5), the recursion

A candidate set whose columns agree outside `k ≥ 4` rows and miss `k + 2` words: the greedy row `g` has at least
two missing words on each side. The total depth is `cdepth |S| + 1` if some side `b` of `g` misses exactly two
words and the missing words of the other side form a ball, and `cdepth |S|` otherwise.
-/

noncomputable section

namespace GradientKey.Concrete

open Finset

variable {n m : ℕ}

/-- If every coordinate separates at most one word of `M` from the others, `|M| ≤ |ι| + 1`. -/
theorem card_le_of_sep {ι : Type*} [Fintype ι] [DecidableEq ι] (M : Finset (ι → Bool))
    (hsep : ∀ x, (M.filter (fun p => p x = true)).card ≤ 1 ∨
      (M.filter (fun p => p x = false)).card ≤ 1) : M.card ≤ Fintype.card ι + 1 := by
  classical
  let c : ι → Bool := fun x => decide (2 ≤ (M.filter (fun p => p x = true)).card)
  have hminor : ∀ x, (M.filter (fun p => p x ≠ c x)).card ≤ 1 := by
    intro x
    by_cases h2 : 2 ≤ (M.filter (fun p => p x = true)).card
    · have hcx : c x = true := by simp [c, h2]
      have : (M.filter (fun p => p x = false)).card ≤ 1 := by
        rcases hsep x with h | h
        · omega
        · exact h
      simpa [hcx] using this
    · have hcx : c x = false := by simp [c, h2]
      simpa [hcx] using (show (M.filter (fun p => p x = true)).card ≤ 1 by omega)
  let D : (ι → Bool) → Finset ι := fun p => univ.filter (fun x => p x ≠ c x)
  have hdisj : (M : Set (ι → Bool)).PairwiseDisjoint D := by
    intro p hp q hq hpq
    rw [Function.onFun, disjoint_left]
    intro x hxp hxq
    simp only [D, mem_filter, mem_univ, true_and] at hxp hxq
    have : 1 < (M.filter (fun p => p x ≠ c x)).card :=
      one_lt_card.mpr ⟨p, mem_filter.mpr ⟨hp, hxp⟩, q, mem_filter.mpr ⟨hq, hxq⟩, hpq⟩
    have := hminor x
    omega
  have hsum : ∑ p ∈ M, (D p).card ≤ Fintype.card ι := by
    rw [← card_biUnion hdisj, ← card_univ]
    exact card_le_card (subset_univ _)
  have hpos : ∀ p, p ≠ c → 1 ≤ (D p).card := by
    intro p hp
    obtain ⟨x, hx⟩ : ∃ x, p x ≠ c x := by
      by_contra h; push_neg at h; exact hp (funext h)
    exact card_pos.mpr ⟨x, by simp [D, hx]⟩
  have h1 : (M.erase c).card ≤ ∑ p ∈ M.erase c, (D p).card := by
    rw [card_eq_sum_ones]
    exact sum_le_sum (fun p hp => hpos p (ne_of_mem_erase hp))
  have h2 : ∑ p ∈ M.erase c, (D p).card ≤ ∑ p ∈ M, (D p).card :=
    sum_le_sum_of_subset_of_nonneg (erase_subset _ _) (fun _ _ _ => Nat.zero_le _)
  have h3 : M.card ≤ (M.erase c).card + 1 := by
    by_cases hc : c ∈ M
    · rw [card_erase_of_mem hc]; omega
    · rw [erase_eq_of_notMem hc]; omega
  omega

/-- The condition for excess `1`: a side `b` of the greedy row misses two words, and the missing words of the
other side form a ball. -/
def TwoBall (A : Table n m) (hn : 0 < n) (F : Finset (Fin n)) (S : Finset (Fin m)) (k : ℕ) : Prop :=
  ∃ b, (slice A S (greedyRow A S hn) b).card + 2 = 2 ^ (k - 1) ∧
    ∃ c, missing A (F.erase (greedyRow A S hn)) (slice A S (greedyRow A S hn) (!b)) = ball c

open Classical in
set_option maxHeartbeats 2000000 in
theorem near_two (A : Table n m) (hA : DistinctColumns A) (hn : 0 < n) (k : ℕ) (hk : 4 ≤ k)
    (F : Finset (Fin n)) (S : Finset (Fin m)) (hF : F.card = k) (hS : AgreeOff A F S)
    (hM : (missing A F S).card = k + 2) :
    totalDepth A hn S = cdepth S.card + (if TwoBall A hn F S k then 1 else 0) := by
  have hcm := card_missing A hA F S hS
  rw [hF, hM] at hcm
  have hkk := le_two_pow_pred k (by omega)
  have hpk := two_pow_pred k (by omega)
  have h4 := le_two_pow_sub_two k hk
  have hp2 : 2 ^ (k - 1) = 2 * 2 ^ (k - 2) := by
    have := two_pow_pred (k - 1) (by omega)
    rwa [show k - 1 - 1 = k - 2 by omega] at this
  have hS2 : 2 ≤ S.card := by omega
  set g := greedyRow A S hn with hg
  have hgF : g ∈ F := greedy_mem A hA hn F S hS hS2
  have hsm : ∀ (x : Fin n) (hx : x ∈ F) (b : Bool), (slice A S x b).card +
      ((missing A F S).filter (fun p => p ⟨x, hx⟩ = b)).card = 2 ^ (k - 1) := by
    intro x hx b; rw [← hF]; exact slice_add_missing A hA F S hS x hx b
  have hsum : ∀ (x : Fin n) (hx : x ∈ F), ((missing A F S).filter (fun p => p ⟨x, hx⟩ = true)).card +
      ((missing A F S).filter (fun p => p ⟨x, hx⟩ = false)).card = k + 2 := by
    intro x hx; rw [missing_filter_add, hM]
  have hFe : (F.erase g).card = k - 1 := by rw [card_erase_of_mem hgF, hF]
  have hag := agreeOff_slice A F S hS g
  have hdense : ∀ b, ((missing A F S).filter (fun p => p ⟨g, hgF⟩ = b)).card ≤ k - 1 →
      totalDepth A hn (child A hn S b) = cdepth (child A hn S b).card := by
    intro b hb
    have := hsm g hgF b
    exact totalDepth_dense A hA hn (k - 1) (F.erase g) _ hFe (hag b) (by
      change 2 ^ (k - 1) ≤ (slice A S g b).card + (k - 1); omega)
  -- both sides of the greedy row miss at least two words
  have hge2 : ∀ b, 2 ≤ ((missing A F S).filter (fun p => p ⟨g, hgF⟩ = b)).card := by
    by_contra hno
    push_neg at hno
    obtain ⟨b, hb⟩ := hno
    have hqg : quality A S g + (k + 1) ≤ 2 ^ (k - 1) := by
      rw [quality_eq]
      have e1 := hsm g hgF true; have e0 := hsm g hgF false; have es := hsum g hgF
      cases b
      · have := min_le_right (slice A S g true).card (slice A S g false).card; omega
      · have := min_le_left (slice A S g true).card (slice A S g false).card; omega
    have hsep : ∀ x : F, ((missing A F S).filter (fun p => p x = true)).card ≤ 1 ∨
        ((missing A F S).filter (fun p => p x = false)).card ≤ 1 := by
      rintro ⟨x, hx⟩
      have hq := p1_greedy_quality_max A S hn x
      rw [← hg] at hq
      have f1 := hsm x hx true
      have f0 := hsm x hx false
      have fs := hsum x hx
      rw [quality_eq] at hq
      have : min (slice A S x true).card (slice A S x false).card + (k + 1) ≤ 2 ^ (k - 1) := by omega
      rcases min_choice (slice A S x true).card (slice A S x false).card with h | h <;>
        rw [h] at this <;> omega
    have := card_le_of_sep (missing A F S) hsep
    rw [hM, Fintype.card_coe, hF] at this
    omega
  have hadd := child_card_add A hn S
  have c1 : ∀ b, (child A hn S b).card = (slice A S g b).card := fun b => rfl
  by_cases h3 : ∀ b, 3 ≤ ((missing A F S).filter (fun p => p ⟨g, hgF⟩ = b)).card
  · -- both sides miss at least three words: both children are dense, no excess
    have hnt : ¬ TwoBall A hn F S k := by
      rintro ⟨b, hb, -⟩
      have := hsm g hgF b
      have := h3 b
      rw [← hg] at hb
      omega
    rw [if_neg hnt, add_zero, totalDepth_fork A hA hn S hS2]
    have es := hsum g hgF
    have t1 := h3 true; have t0 := h3 false
    rw [hdense true (by omega), hdense false (by omega), ← hadd]
    have e1 := hsm g hgF true; have e0 := hsm g hgF false
    have hk21 : k - 2 + 1 = k - 1 := by omega
    have a1 : 2 ^ (k - 2) ≤ (child A hn S true).card := by rw [c1]; omega
    have a2 : (child A hn S true).card ≤ 2 ^ (k - 2 + 1) := by rw [c1, hk21]; omega
    have b1 : 2 ^ (k - 2) ≤ (child A hn S false).card := by rw [c1]; omega
    have b2 : (child A hn S false).card ≤ 2 ^ (k - 2 + 1) := by rw [c1, hk21]; omega
    have := cdepth_add (k - 2) _ _ a1 a2 b1 b2
    omega
  · -- some side `b` misses exactly two words; the other side misses `k`
    push_neg at h3
    obtain ⟨b, hb⟩ := h3
    have hb2 : ((missing A F S).filter (fun p => p ⟨g, hgF⟩ = b)).card = 2 := by
      have := hge2 b; omega
    have hnb : ((missing A F S).filter (fun p => p ⟨g, hgF⟩ = !b)).card = k := by
      have es := hsum g hgF
      cases b <;> simp only [Bool.not_true, Bool.not_false] <;> omega
    have hsb := hsm g hgF b
    have hsnb := hsm g hgF (!b)
    rw [hb2] at hsb
    rw [hnb] at hsnb
    have hcb : (child A hn S b).card = 2 ^ (k - 1) - 2 := by rw [c1]; omega
    have hcnb : (child A hn S (!b)).card = 2 ^ (k - 1) - k := by rw [c1]; omega
    have hdb := hdense b (by rw [hb2]; omega)
    -- the other side: `k = (k-1) + 1` missing words in dimension `k - 1 ≥ 3`
    have hcard' : (missing A (F.erase g) (child A hn S (!b))).card = (k - 1) + 1 := by
      have := card_missing A hA (F.erase g) (child A hn S (!b)) (hag (!b))
      rw [hFe, hcnb] at this
      have := Nat.sub_add_cancel (show k ≤ 2 ^ (k - 1) by omega)
      omega
    have hnear := near_ball A hA hn (k - 1) (by omega) (F.erase g) (child A hn S (!b)) hFe (hag (!b))
      hcard'
    have hiff : TwoBall A hn F S k ↔ ∃ c, missing A (F.erase g) (child A hn S (!b)) = ball c := by
      constructor
      · rintro ⟨b', hb', hc⟩
        rw [← hg] at hb' hc
        have hbb : b' = b := by
          by_contra hne
          have : b' = !b := by cases b <;> cases b' <;> simp_all
          subst this
          have := hsm g hgF (!b)
          omega
        subst hbb
        exact hc
      · intro hc
        exact ⟨b, by rw [← hg]; omega, by rw [← hg]; exact hc⟩
    rw [totalDepth_fork_side A hA hn S hS2 b, hdb, hnear]
    have hsizes : S.card = (child A hn S b).card + (child A hn S (!b)).card := by
      cases b <;> simp <;> omega
    have hk21 : k - 2 + 1 = k - 1 := by omega
    have a1 : 2 ^ (k - 2) ≤ (child A hn S b).card := by rw [hcb]; omega
    have a2 : (child A hn S b).card ≤ 2 ^ (k - 2 + 1) := by rw [hcb, hk21]; omega
    have b1 : 2 ^ (k - 2) ≤ (child A hn S (!b)).card := by rw [hcnb]; omega
    have b2 : (child A hn S (!b)).card ≤ 2 ^ (k - 2 + 1) := by rw [hcnb, hk21]; omega
    have := cdepth_add (k - 2) _ _ a1 a2 b1 b2
    by_cases hball : ∃ c, missing A (F.erase g) (child A hn S (!b)) = ball c
    · rw [if_pos hball, if_pos (hiff.mpr hball), hsizes]; omega
    · rw [if_neg hball, if_neg (fun h => hball (hiff.mp h)), hsizes]; omega

end GradientKey.Concrete
