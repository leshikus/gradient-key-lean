import Missing

/-!
# `k + 1` missing words (first case of Proposition 3.5)

A candidate set whose columns agree outside `k ≥ 3` rows and miss `k + 1` words of `{0,1}^k` has total depth
`cdepth |S| + 1` if the missing words form a ball of radius `1`, and `cdepth |S|` otherwise.
-/

noncomputable section

namespace GradientKey.Concrete

open Finset

variable {n m : ℕ}

theorem le_two_pow_sub_two (k : ℕ) (hk : 4 ≤ k) : k ≤ 2 ^ (k - 2) := by
  induction k, hk using Nat.le_induction with
  | base => norm_num
  | succ k hk ih =>
    have : 2 ^ (k + 1 - 2) = 2 * 2 ^ (k - 2) := by
      rw [← pow_succ']; congr 1; omega
    omega

theorem cdepth_one : cdepth 1 = 0 := by simp [cdepth]

theorem cdepth_three : cdepth 3 = 5 := by
  rw [cdepth_eq 1 3 (by norm_num) (by norm_num)]; norm_num

theorem cdepth_four : cdepth 4 = 8 := by
  rw [cdepth_eq 2 4 (by norm_num) (by norm_num)]; norm_num

theorem two_pow_pred (k : ℕ) (hk : 1 ≤ k) : 2 ^ k = 2 * 2 ^ (k - 1) := by
  rw [← pow_succ']; congr 1; omega

theorem greedy_mem (A : Table n m) (hA : DistinctColumns A) (hn : 0 < n) (F : Finset (Fin n))
    (S : Finset (Fin m)) (hS : AgreeOff A F S) (hS2 : 2 ≤ S.card) : greedyRow A S hn ∈ F := by
  obtain ⟨j, hj⟩ : S.Nonempty := card_pos.mp (by omega)
  by_contra hgF
  obtain ⟨k', hk', hd⟩ := p1_opposite_of_quality_pos A S (greedyRow A S hn) j
    (p1_greedy_quality_pos A hA S j hn hj hS2)
  exact hd (hS k' hk' j hj _ hgF)

theorem totalDepth_fork_side (A : Table n m) (hA : DistinctColumns A) (hn : 0 < n)
    (S : Finset (Fin m)) (hS : 2 ≤ S.card) (b : Bool) :
    totalDepth A hn S = S.card + totalDepth A hn (child A hn S b) + totalDepth A hn (child A hn S (!b)) := by
  rw [totalDepth_fork A hA hn S hS]
  cases b <;> simp <;> ring

theorem quality_eq (A : Table n m) (S : Finset (Fin m)) (r : Fin n) :
    quality A S r = min (slice A S r true).card (slice A S r false).card := rfl

theorem missing_filter_add (A : Table n m) (F : Finset (Fin n)) (S : Finset (Fin m)) (x : F) :
    ((missing A F S).filter (fun p => p x = true)).card +
      ((missing A F S).filter (fun p => p x = false)).card = (missing A F S).card := by
  have := card_filter_add_card_filter_not (s := missing A F S) (fun p => p x = true)
  simpa using this

set_option maxHeartbeats 2000000 in
theorem near_ball (A : Table n m) (hA : DistinctColumns A) (hn : 0 < n) (k : ℕ) (hk : 3 ≤ k)
    (F : Finset (Fin n)) (S : Finset (Fin m)) (hF : F.card = k) (hS : AgreeOff A F S)
    (hM : (missing A F S).card = k + 1) :
    totalDepth A hn S = cdepth S.card + (if ∃ c, missing A F S = ball c then 1 else 0) := by
  induction k using Nat.strong_induction_on generalizing F S with
  | _ k ih =>
  have hcm := card_missing A hA F S hS
  rw [hF, hM] at hcm
  have hkk := le_two_pow_pred k (by omega)
  have hpk := two_pow_pred k (by omega)
  have hS2 : 2 ≤ S.card := by omega
  set g := greedyRow A S hn with hg
  have hgF : g ∈ F := greedy_mem A hA hn F S hS hS2
  -- sizes of the children of row `x` and the missing words on each side
  have hsm : ∀ (x : Fin n) (hx : x ∈ F) (b : Bool), (slice A S x b).card +
      ((missing A F S).filter (fun p => p ⟨x, hx⟩ = b)).card = 2 ^ (k - 1) := by
    intro x hx b; rw [← hF]; exact slice_add_missing A hA F S hS x hx b
  have hsum : ∀ (x : Fin n) (hx : x ∈ F), ((missing A F S).filter (fun p => p ⟨x, hx⟩ = true)).card +
      ((missing A F S).filter (fun p => p ⟨x, hx⟩ = false)).card = k + 1 := by
    intro x hx; rw [missing_filter_add, hM]
  have hFe : (F.erase g).card = k - 1 := by rw [card_erase_of_mem hgF, hF]
  have hag := agreeOff_slice A F S hS g
  -- the dense case for a child with at most `k - 1` missing words
  have hdense : ∀ b, ((missing A F S).filter (fun p => p ⟨g, hgF⟩ = b)).card ≤ k - 1 →
      totalDepth A hn (child A hn S b) = cdepth (child A hn S b).card := by
    intro b hb
    have := hsm g hgF b
    exact totalDepth_dense A hA hn (k - 1) (F.erase g) _ hFe (hag b) (by
      change 2 ^ (k - 1) ≤ (slice A S g b).card + (k - 1); omega)
  set r1 := ((missing A F S).filter (fun p => p ⟨g, hgF⟩ = true)).card with hr1
  set r0 := ((missing A F S).filter (fun p => p ⟨g, hgF⟩ = false)).card with hr0
  have e1 := hsm g hgF true
  have e0 := hsm g hgF false
  have es := hsum g hgF
  rw [← hr1] at e1 es; rw [← hr0] at e0 es
  have c1 : (child A hn S true).card = (slice A S g true).card := rfl
  have c0 : (child A hn S false).card = (slice A S g false).card := rfl
  have hadd := child_card_add A hn S
  by_cases hA2 : 2 ≤ r1 ∧ 2 ≤ r0
  · -- both sides miss at least two words: both children are dense
    have hnb : ¬∃ c, missing A F S = ball c := by
      rintro ⟨c, hc⟩
      have h1 := ball_filter_flip c ⟨g, hgF⟩
      rw [← hc] at h1
      cases hcg : c ⟨g, hgF⟩
      · rw [hcg] at h1; simp only [Bool.not_false] at h1
        have : r1 = 1 := by rw [hr1, h1, card_singleton]
        omega
      · rw [hcg] at h1; simp only [Bool.not_true] at h1
        have : r0 = 1 := by rw [hr0, h1, card_singleton]
        omega
    rw [if_neg hnb, add_zero, totalDepth_fork A hA hn S hS2, hdense true (by omega),
      hdense false (by omega), ← hadd]
    have h2 := le_two_pow_pred (k - 1) (by omega)
    have hp2 := two_pow_pred (k - 1) (by omega)
    have := cdepth_add (k - 2) (child A hn S true).card (child A hn S false).card
      (by rw [show k - 2 = k - 1 - 1 by omega]; omega)
      (by rw [show k - 2 + 1 = k - 1 by omega]; omega)
      (by rw [show k - 2 = k - 1 - 1 by omega]; omega)
      (by rw [show k - 2 + 1 = k - 1 by omega]; omega)
    omega
  · -- some side of the greedy row misses at most one word: the missing words form a ball
    have hqg : quality A S g + k ≤ 2 ^ (k - 1) := by
      rw [quality_eq]
      rcases not_and_or.mp hA2 with h | h
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
      have : min (slice A S x true).card (slice A S x false).card + k ≤ 2 ^ (k - 1) := by omega
      rcases min_choice (slice A S x true).card (slice A S x false).card with h | h <;>
        rw [h] at this <;> omega
    obtain ⟨c, hc⟩ := isBall_of_sep (missing A F S) (by rw [hM, Fintype.card_coe, hF]) hsep
    rw [if_pos ⟨c, hc⟩]
    set b := c ⟨g, hgF⟩ with hb
    -- side `!b` misses one word, side `b` misses the other `k`
    have hflip := ball_filter_flip c ⟨g, hgF⟩
    have hsame := ball_filter_same c ⟨g, hgF⟩
    rw [← hc] at hflip hsame
    rw [Fintype.card_coe, hF] at hsame
    have hrb : ((missing A F S).filter (fun p => p ⟨g, hgF⟩ = !b)).card = 1 := by
      rw [hflip, card_singleton]
    have hsb := hsm g hgF b
    have hsnb := hsm g hgF (!b)
    rw [hsame] at hsb
    rw [hrb] at hsnb
    have hcb : (child A hn S b).card = 2 ^ (k - 1) - k := by
      change (slice A S g b).card = _; omega
    have hcnb : (child A hn S (!b)).card = 2 ^ (k - 1) - 1 := by
      change (slice A S g (!b)).card = _; omega
    have hdnb := hdense (!b) (by rw [hrb]; omega)
    rw [totalDepth_fork_side A hA hn S hS2 b, hdnb]
    have hsizes : S.card = (child A hn S b).card + (child A hn S (!b)).card := by
      cases b <;> simp <;> omega
    rcases Nat.lt_or_ge k 4 with hk4 | hk4
    · -- `k = 3`: the side `b` is a single column
      have hk3 : k = 3 := by omega
      rw [hk3] at hcb hcnb
      norm_num at hcb hcnb
      rw [totalDepth_le_one A hn _ (by omega), hsizes, hcb, hcnb, cdepth_three,
        show (1 : ℕ) + 3 = 4 from rfl, cdepth_four]
    · -- `k ≥ 4`: induction on the side `b`
      have hball := missing_slice_ball A F S g hgF c hc
      have hcard' : (missing A (F.erase g) (child A hn S b)).card = (k - 1) + 1 := by
        change (missing A (F.erase g) (slice A S g b)).card = _
        rw [hball, card_ball, Fintype.card_coe, hFe]
      have hih := ih (k - 1) (by omega) (by omega) (F.erase g) (child A hn S b) hFe (hag b) hcard'
      rw [if_pos ⟨resW F g c, hball⟩] at hih
      rw [hih]
      have h4 := le_two_pow_sub_two k hk4
      have hp2 : 2 ^ (k - 1) = 2 * 2 ^ (k - 2) := by
        have := two_pow_pred (k - 1) (by omega)
        rwa [show k - 1 - 1 = k - 2 by omega] at this
      have hk21 : k - 2 + 1 = k - 1 := by omega
      have hb1 : 2 ^ (k - 2) ≤ (child A hn S b).card := by rw [hcb]; omega
      have hb2 : (child A hn S b).card ≤ 2 ^ (k - 2 + 1) := by rw [hcb, hk21]; omega
      have hnb1 : 2 ^ (k - 2) ≤ (child A hn S (!b)).card := by rw [hcnb]; omega
      have hnb2 : (child A hn S (!b)).card ≤ 2 ^ (k - 2 + 1) := by rw [hcnb, hk21]; omega
      have := cdepth_add (k - 2) _ _ hb1 hb2 hnb1 hnb2
      rw [hsizes]
      omega

end GradientKey.Concrete
