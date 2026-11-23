import PathCoeff

/-!
# Proposition 3.2: `∑_{π of type u} μ(π) = c(u)`

`typeVec c v` is the number of blocks of size `v` of the set partition `c` of `Fin a`, and
`tsum a u = ∑_{c of type u} μ(c)`. Extending a partition of `Fin a` by a singleton block or by
enlarging one block gives every partition of `Fin (a+1)` once, so `tsum` satisfies the recurrence
`coef_rec` of `coefB`; by induction `tsum a u = coefB B a u` for every type `u` of an `a`-set.
-/

noncomputable section

namespace GradientKey.Concrete

open Finset Classical

/-- The number of blocks of size `v`. -/
def typeVec {a : ℕ} (c : OrderedFinpartition a) (v : ℕ) : ℕ :=
  (univ.filter (fun k => c.partSize k = v)).card

/-- The sum of the Möbius weights of the set partitions of `Fin a` of type `u`. -/
def tsum (a : ℕ) (u : ℕ → ℕ) : ℚ :=
  ∑ c : OrderedFinpartition a, if typeVec c = u then (mu c : ℚ) else 0

theorem length_zero (c : OrderedFinpartition 0) : c.length = 0 := by
  by_contra h
  exact Fin.elim0 (c.emb ⟨0, by omega⟩ ⟨0, c.partSize_pos _⟩)

theorem typeVec_extendLeft {a : ℕ} (c : OrderedFinpartition a) (v : ℕ) :
    typeVec c.extendLeft v = typeVec c v + (if 1 = v then 1 else 0) := by
  unfold typeVec
  rw [card_filter, card_filter]
  show ∑ i : Fin (c.length + 1),
      (if (Fin.cons (1 : ℕ) c.partSize : Fin (c.length + 1) → ℕ) i = v then 1 else 0) = _
  rw [Fin.sum_univ_succ]
  simp only [Fin.cons_zero, Fin.cons_succ]
  ring

theorem sum_update_fin {ι : Type*} [Fintype ι] [DecidableEq ι] (g : ℕ → ℕ) (f : ι → ℕ) (k : ι)
    (x : ℕ) : ∑ i, g (Function.update f k x i) + g (f k) = ∑ i, g (f i) + g x := by
  have e : (fun i => g (Function.update f k x i)) = Function.update (fun i => g (f i)) k (g x) := by
    funext i
    by_cases h : i = k
    · subst h; simp
    · simp [h]
  rw [e, sum_update_of_mem (mem_univ k), ← add_sum_erase univ (fun i => g (f i)) (mem_univ k),
    sdiff_singleton_eq_erase]
  ring

theorem typeVec_extendMiddle {a : ℕ} (c : OrderedFinpartition a) (k : Fin c.length) (v : ℕ) :
    typeVec (c.extendMiddle k) v + (if c.partSize k = v then 1 else 0) =
      typeVec c v + (if c.partSize k + 1 = v then 1 else 0) := by
  unfold typeVec
  rw [card_filter, card_filter]
  show ∑ i : Fin c.length,
      (if Function.update c.partSize k (c.partSize k + 1) i = v then 1 else 0) + _ = _
  exact sum_update_fin (fun y => if y = v then 1 else 0) c.partSize k (c.partSize k + 1)

theorem sum_partSize : ∀ {a : ℕ} (c : OrderedFinpartition a), ∑ k, c.partSize k = a
  | 0, c => by
    have := length_zero c
    exact Finset.sum_eq_zero (fun k _ => absurd k.isLt (by omega))
  | a + 1, c' => by
    obtain ⟨⟨c, o⟩, rfl⟩ := (OrderedFinpartition.extendEquiv a).surjective c'
    cases o with
    | none =>
      show ∑ i : Fin (c.length + 1), (Fin.cons (1 : ℕ) c.partSize : Fin (c.length + 1) → ℕ) i = _
      rw [Fin.sum_univ_succ]
      simp only [Fin.cons_zero, Fin.cons_succ]
      rw [sum_partSize c]
      ring
    | some k =>
      show ∑ i : Fin c.length, Function.update c.partSize k (c.partSize k + 1) i = _
      have := sum_update_fin id c.partSize k (c.partSize k + 1)
      simp only [id] at this
      rw [sum_partSize c] at this
      omega

theorem typeVec_isTy {a B : ℕ} (c : OrderedFinpartition a) (hB : a < B) : IsTy B a (typeVec c) := by
  refine ⟨?_, ?_, ?_⟩
  · unfold typeVec
    rw [card_eq_zero, filter_eq_empty_iff]
    intro k _
    exact (c.partSize_pos k).ne'
  · intro v hv
    unfold typeVec
    rw [card_eq_zero, filter_eq_empty_iff]
    intro k _
    have := c.partSize_le k
    omega
  · unfold wt typeVec
    have hmaps : ∀ k ∈ (univ : Finset (Fin c.length)), c.partSize k ∈ range B := by
      intro k _
      have := c.partSize_le k
      exact mem_range.mpr (by omega)
    refine Eq.trans ?_ (sum_partSize c)
    rw [← sum_fiberwise_of_maps_to hmaps]
    apply sum_congr rfl
    intro v _
    rw [sum_congr rfl (fun k hk => (mem_filter.mp hk).2), sum_const, smul_eq_mul, mul_comm]

/-- `tvec(extendLeft c) = u` iff `u` has a block of size `1` and `tvec c = rem1 u`. -/
theorem extendLeft_type_iff {a : ℕ} (c : OrderedFinpartition a) (u : ℕ → ℕ) :
    typeVec c.extendLeft = u ↔ 1 ≤ u 1 ∧ typeVec c = rem1 u := by
  have h := typeVec_extendLeft c
  constructor
  · intro hu
    subst hu
    refine ⟨by rw [h 1]; simp, ?_⟩
    funext v
    unfold rem1
    by_cases hv : v = 1
    · subst hv; simp [h 1]
    · rw [Function.update_of_ne hv, h v, if_neg (Ne.symm hv), add_zero]
  · rintro ⟨h1, hc⟩
    funext v
    rw [h v, hc]
    unfold rem1
    by_cases hv : v = 1
    · subst hv; simp; omega
    · rw [Function.update_of_ne hv, if_neg (Ne.symm hv), add_zero]

/-- `tvec(extendMiddle c k) = u` iff, with `s` the size of block `k`, `u` has a block of size `s+1`
and `tvec c = remv u s`. -/
theorem extendMiddle_type_iff {a : ℕ} (c : OrderedFinpartition a) (k : Fin c.length) (u : ℕ → ℕ) :
    typeVec (c.extendMiddle k) = u ↔
      1 ≤ u (c.partSize k + 1) ∧ typeVec c = remv u (c.partSize k) := by
  have h := typeVec_extendMiddle c k
  set s := c.partSize k
  have hs1 : ¬ (s = s + 1) := by omega
  have hs2 : ¬ (s + 1 = s) := by omega
  constructor
  · intro hu
    subst hu
    have h1 := h (s + 1)
    rw [if_neg hs1, if_pos rfl] at h1
    refine ⟨by omega, ?_⟩
    funext v
    unfold remv
    by_cases hv1 : v = s + 1
    · rw [hv1, Function.update_self]; omega
    · rw [Function.update_of_ne hv1]
      by_cases hv : v = s
      · rw [hv, Function.update_self]
        have h2 := h s
        rw [if_pos rfl, if_neg hs2] at h2
        omega
      · rw [Function.update_of_ne hv]
        have h3 := h v
        rw [if_neg (Ne.symm hv), if_neg (Ne.symm hv1)] at h3
        omega
  · rintro ⟨h1, hc⟩
    funext v
    have hv' := h v
    rw [hc] at hv'
    unfold remv at hv'
    by_cases hv1 : v = s + 1
    · rw [hv1, Function.update_self, if_neg hs1, if_pos rfl] at hv'
      rw [hv1]; omega
    · rw [Function.update_of_ne hv1] at hv'
      by_cases hv : v = s
      · rw [hv, Function.update_self, if_pos rfl, if_neg hs2] at hv'
        rw [hv]; omega
      · rw [Function.update_of_ne hv, if_neg (Ne.symm hv), if_neg (Ne.symm hv1)] at hv'
        omega

/-- **Recurrence for `tsum`.** -/
theorem tsum_rec (a : ℕ) (u : ℕ → ℕ) :
    tsum (a + 1) u =
      (if 1 ≤ u 1 then tsum a (rem1 u) else 0) +
        ∑ t ∈ range a, (if 1 ≤ u (t + 2) then
          -((t : ℚ) + 1) * ((u (t + 1) : ℚ) + 1) * tsum a (remv u (t + 1)) else 0) := by
  unfold tsum
  rw [← (OrderedFinpartition.extendEquiv a).sum_comp, Fintype.sum_sigma]
  have hsplit : ∀ c : OrderedFinpartition a,
      (∑ o : Option (Fin c.length),
        if typeVec ((OrderedFinpartition.extendEquiv a) ⟨c, o⟩) = u then
          ((mu ((OrderedFinpartition.extendEquiv a) ⟨c, o⟩) : ℤ) : ℚ) else 0) =
      (if typeVec c.extendLeft = u then ((mu c.extendLeft : ℤ) : ℚ) else 0) +
        ∑ k, (if typeVec (c.extendMiddle k) = u then ((mu (c.extendMiddle k) : ℤ) : ℚ) else 0) :=
    fun c => Fintype.sum_option _
  rw [sum_congr rfl (fun c _ => hsplit c), sum_add_distrib]
  congr 1
  · -- new singleton block
    simp only [extendLeft_type_iff, mu_extendLeft]
    split_ifs with h1
    · simp only [h1, true_and]
    · simp only [h1, false_and, if_false, sum_const_zero]
  · -- enlarged block
    have hterm : ∀ c : OrderedFinpartition a, ∀ k : Fin c.length,
        (if typeVec (c.extendMiddle k) = u then ((mu (c.extendMiddle k) : ℤ) : ℚ) else 0) =
          if 1 ≤ u (c.partSize k + 1) ∧ typeVec c = remv u (c.partSize k) then
            -(c.partSize k : ℚ) * (mu c : ℚ) else 0 := by
      intro c k
      rw [mu_extendMiddle]
      push_cast
      exact if_congr (extendMiddle_type_iff c k u) rfl rfl
    simp only [hterm]
    -- group the blocks by size `t + 1`
    have hgroup : ∀ c : OrderedFinpartition a,
        (∑ k : Fin c.length, if 1 ≤ u (c.partSize k + 1) ∧ typeVec c = remv u (c.partSize k) then
            -(c.partSize k : ℚ) * (mu c : ℚ) else 0) =
          ∑ t ∈ range a, if 1 ≤ u (t + 2) ∧ typeVec c = remv u (t + 1) then
            -((t : ℚ) + 1) * ((u (t + 1) : ℚ) + 1) * (mu c : ℚ) else 0 := by
      intro c
      have hmaps : ∀ k ∈ (univ : Finset (Fin c.length)), c.partSize k - 1 ∈ range a := by
        intro k _
        have h1 := c.partSize_le k
        have h2 := c.partSize_pos k
        exact mem_range.mpr (by omega)
      rw [← sum_fiberwise_of_maps_to hmaps]
      apply sum_congr rfl
      intro t _
      have hfib : ∀ k ∈ univ.filter (fun k : Fin c.length => c.partSize k - 1 = t),
          c.partSize k = t + 1 := by
        intro k hk
        have := (mem_filter.mp hk).2
        have h2 := c.partSize_pos k
        omega
      rw [sum_congr rfl (fun k hk => by rw [hfib k hk]), sum_const, nsmul_eq_mul]
      have hcard : (univ.filter (fun k : Fin c.length => c.partSize k - 1 = t)).card =
          typeVec c (t + 1) := by
        unfold typeVec
        congr 1
        apply filter_congr
        intro k _
        have h2 := c.partSize_pos k
        omega
      rw [hcard]
      split_ifs with hc
      · rw [hc.2]
        unfold remv
        simp only [Function.update_self, show t + 1 ≠ t + 1 + 1 by omega, Function.update_of_ne,
          ne_eq, not_false_eq_true]
        push_cast
        ring
      · simp
    rw [sum_congr rfl (fun c _ => hgroup c), sum_comm]
    apply sum_congr rfl
    intro t _
    split_ifs with h2
    · rw [mul_sum]
      apply sum_congr rfl
      intro c _
      simp only [h2, true_and]
      split_ifs <;> ring
    · simp [h2]

/-- A type of an `a`-set with a block of size `1` stays a type after removing it. -/
theorem isTy_rem1 {B a : ℕ} {u : ℕ → ℕ} (hB : a + 2 ≤ B) (hu : IsTy B (a + 1) u) (h1 : 1 ≤ u 1) :
    IsTy B a (rem1 u) := by
  refine ⟨by unfold rem1; rw [Function.update_of_ne (by omega)]; exact hu.1, ?_, ?_⟩
  · intro v hv
    unfold rem1
    rw [Function.update_of_ne (by omega)]
    exact hu.2.1 v hv
  · have := sum_update_nat (B := B) (fun v y => v * y) u (mem_range.mpr (by omega) : 1 ∈ range B)
      (u 1 - 1)
    beta_reduce at this
    have hw := hu.2.2
    unfold wt at hw
    unfold wt rem1
    omega

theorem isTy_remv {B a : ℕ} {u : ℕ → ℕ} (hB : a + 2 ≤ B) (hu : IsTy B (a + 1) u) {v : ℕ}
    (hv1 : 1 ≤ v) (hva : v ≤ a) (h : 1 ≤ u (v + 1)) : IsTy B a (remv u v) := by
  refine ⟨?_, ?_, ?_⟩
  · unfold remv
    rw [Function.update_of_ne (by omega), Function.update_of_ne (by omega)]
    exact hu.1
  · intro w hw
    unfold remv
    rw [Function.update_of_ne (by omega), Function.update_of_ne (by omega)]
    exact hu.2.1 w hw
  · have hvB : v ∈ range B := mem_range.mpr (by omega)
    have hv1B : v + 1 ∈ range B := mem_range.mpr (by omega)
    set u1 := Function.update u v (u v + 1) with hu1
    have e1 := sum_update_nat (B := B) (fun w y => w * y) u hvB (u v + 1)
    have e2 := sum_update_nat (B := B) (fun w y => w * y) u1 hv1B (u (v + 1) - 1)
    beta_reduce at e1 e2
    rw [← hu1] at e1
    have hu1v : u1 (v + 1) = u (v + 1) := by simp [u1]
    rw [hu1v] at e2
    have hw := hu.2.2
    unfold wt at hw
    unfold wt remv
    rw [← hu1]
    obtain ⟨y, hy⟩ : ∃ y, u (v + 1) = y + 1 := ⟨u (v + 1) - 1, by omega⟩
    rw [hy, Nat.add_sub_cancel] at e2
    rw [hy, Nat.add_sub_cancel]
    nlinarith [e1, e2, hw]

/-- **The Möbius weight of a partition type.** For every type `u` of an `a`-set, the sum of `μ(π)` over
the set partitions `π` of `Fin a` of type `u` is the article's `c(u)`. -/
theorem tsum_eq_coef : ∀ (a B : ℕ), a < B → ∀ u, IsTy B a u → tsum a u = coefB B a u
  | 0, B, hB, u, hu => by
    have hu0 : u = fun _ => 0 := by
      funext v
      by_cases hv : v = 0
      · subst hv; exact hu.1
      · exact hu.zero_of_lt (by omega)
    subst hu0
    have hc : ∀ c : OrderedFinpartition 0, typeVec c = fun _ => 0 := by
      intro c
      funext v
      unfold typeVec
      rw [card_eq_zero, filter_eq_empty_iff]
      intro k _
      exact absurd k.isLt (by have := length_zero c; omega)
    unfold tsum coefB
    rw [Fintype.sum_unique, if_pos (hc _)]
    have hmu : mu (default : OrderedFinpartition 0) = 1 := by
      unfold mu
      exact Finset.prod_eq_one (fun k _ => absurd k.isLt
        (by have := length_zero (default : OrderedFinpartition 0); omega))
    have hP : Pq B (fun _ => 0) = 1 := by
      unfold Pq fw
      simp
    rw [hmu, hP]
    simp
  | a + 1, B, hB, u, hu => by
    rw [tsum_rec, coef_rec (by omega) hu]
    congr 1
    · split_ifs with h1
      · exact tsum_eq_coef a B (by omega) _ (isTy_rem1 (by omega) hu h1)
      · rfl
    · apply sum_congr rfl
      intro t ht
      split_ifs with h2
      · rw [tsum_eq_coef a B (by omega) _ (isTy_remv (by omega) hu (v := t + 1) (by omega)
          (by simp at ht; omega) h2)]
      · rfl

/-- **Grouping by type.** A Möbius-weighted sum of a function of the type is a sum over types with the
coefficients `c`. -/
theorem sum_mu_by_type {a B : ℕ} (hB : a < B) (T : Finset (ℕ → ℕ))
    (hT : ∀ c : OrderedFinpartition a, typeVec c ∈ T) (hTy : ∀ u ∈ T, IsTy B a u)
    (F : (ℕ → ℕ) → ℚ) :
    ∑ c : OrderedFinpartition a, (mu c : ℚ) * F (typeVec c) = ∑ u ∈ T, coefB B a u * F u := by
  rw [← sum_fiberwise_of_maps_to (fun c _ => hT c)]
  apply sum_congr rfl
  intro u hu
  rw [← tsum_eq_coef a B hB u (hTy u hu), tsum, sum_mul]
  rw [sum_filter]
  apply sum_congr rfl
  intro c _
  split_ifs with h
  · rw [h]
  · simp

end GradientKey.Concrete
