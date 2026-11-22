import Mathlib

/-!
# Möbius inversion on the set partitions of `Fin m`

Set partitions of `Fin m` are Mathlib's `OrderedFinpartition m` (parts ordered by their largest element). With
`μ(π) = ∏_B (-1)^{|B|-1} (|B|-1)!`, for every map `x : Fin m → β`,
`∑_π μ(π) [x is constant on each block of π] = [x is injective]`.
The proof adds the element `0` either as a new block or to an existing block (`extendEquiv`).
-/

noncomputable section

namespace GradientKey.Concrete

open Finset OrderedFinpartition

/-- `f(k) = (-1)^{k-1} (k-1)!`. -/
def mobF (k : ℕ) : ℤ := (-1) ^ (k - 1) * ((k - 1).factorial : ℤ)

theorem mobF_one : mobF 1 = 1 := by simp [mobF]

theorem mobF_succ (s : ℕ) (hs : 1 ≤ s) : mobF (s + 1) = -(s : ℤ) * mobF s := by
  unfold mobF
  obtain ⟨t, rfl⟩ : ∃ t, s = t + 1 := ⟨s - 1, by omega⟩
  simp only [Nat.add_sub_cancel, Nat.factorial_succ]
  push_cast
  ring

/-- `μ(π)`. -/
def mu {m : ℕ} (c : OrderedFinpartition m) : ℤ := ∏ i, mobF (c.partSize i)

/-- `x` is constant on each block of `c`. -/
def ConstOn {m : ℕ} {β : Type*} (c : OrderedFinpartition m) (x : Fin m → β) : Prop :=
  ∀ i (t t' : Fin (c.partSize i)), x (c.emb i t) = x (c.emb i t')

theorem mu_extendLeft {m : ℕ} (c : OrderedFinpartition m) : mu c.extendLeft = mu c := by
  unfold mu
  show ∏ i : Fin (c.length + 1), mobF ((Fin.cons (1 : ℕ) c.partSize : Fin (c.length + 1) → ℕ) i) = _
  rw [Fin.prod_univ_succ]
  simp [mobF_one]

theorem mu_extendMiddle {m : ℕ} (c : OrderedFinpartition m) (k : Fin c.length) :
    mu (c.extendMiddle k) = -(c.partSize k : ℤ) * mu c := by
  unfold mu
  show ∏ i : Fin c.length, mobF (Function.update c.partSize k (c.partSize k + 1) i) = _
  have : ∀ i, mobF (Function.update c.partSize k (c.partSize k + 1) i) =
      Function.update (fun i => mobF (c.partSize i)) k (mobF (c.partSize k + 1)) i := by
    intro i; by_cases h : i = k
    · subst h; simp
    · simp [h]
  simp only [this]
  rw [Finset.prod_update_of_mem (mem_univ k), mobF_succ _ (c.partSize_pos k),
    ← Finset.mul_prod_erase univ _ (mem_univ k), sdiff_singleton_eq_erase]
  ring

theorem constOn_extendLeft {m : ℕ} {β : Type*} (c : OrderedFinpartition m) (x : Fin (m + 1) → β) :
    ConstOn c.extendLeft x ↔ ConstOn c (Fin.tail x) := by
  unfold ConstOn
  constructor
  · intro h i t t'
    exact h i.succ t t'
  · intro h i
    induction i using Fin.cases with
    | zero => intro t t'; simp [extendLeft]
    | succ i =>
      intro t t'
      exact h i t t'

theorem constOn_iff_range {m : ℕ} {β : Type*} (c : OrderedFinpartition m) (x : Fin m → β) :
    ConstOn c x ↔ ∀ i, ∀ a ∈ Set.range (c.emb i), ∀ b ∈ Set.range (c.emb i), x a = x b := by
  unfold ConstOn
  constructor
  · rintro h i _ ⟨t, rfl⟩ _ ⟨t', rfl⟩; exact h i t t'
  · intro h i t t'; exact h i _ ⟨t, rfl⟩ _ ⟨t', rfl⟩

theorem range_extendMiddle_self {m : ℕ} (c : OrderedFinpartition m) (k : Fin c.length) :
    Set.range ((c.extendMiddle k).emb k) = insert 0 (Fin.succ '' Set.range (c.emb k)) := by
  ext y
  simp only [extendMiddle, ↓reduceDIte, Set.mem_range, Function.comp_apply, Set.mem_insert_iff,
    Set.mem_image]
  constructor
  · rintro ⟨t, rfl⟩
    rcases Fin.eq_zero_or_eq_succ (Fin.cast (by simp) t : Fin (c.partSize k + 1)) with h | ⟨u, hu⟩
    · left; rw [h]; rfl
    · right; exact ⟨c.emb k u, ⟨u, rfl⟩, by rw [hu]; rfl⟩
  · rintro (rfl | ⟨_, ⟨u, rfl⟩, rfl⟩)
    · exact ⟨Fin.cast (by simp) (0 : Fin (c.partSize k + 1)), by simp⟩
    · exact ⟨Fin.cast (by simp) (u.succ : Fin (c.partSize k + 1)), by simp⟩

theorem range_extendMiddle_ne {m : ℕ} (c : OrderedFinpartition m) (k : Fin c.length) {i : Fin c.length}
    (h : i ≠ k) : Set.range ((c.extendMiddle k).emb i) = Fin.succ '' Set.range (c.emb i) := by
  ext y
  simp only [extendMiddle, h, ↓reduceDIte, Set.mem_range, Function.comp_apply, Set.mem_image]
  constructor
  · rintro ⟨t, rfl⟩; exact ⟨_, ⟨_, rfl⟩, rfl⟩
  · rintro ⟨_, ⟨u, rfl⟩, rfl⟩; exact ⟨Fin.cast (by simp [h]) u, by simp⟩

theorem constOn_extendMiddle {m : ℕ} {β : Type*} (c : OrderedFinpartition m) (k : Fin c.length)
    (x : Fin (m + 1) → β) :
    ConstOn (c.extendMiddle k) x ↔ ConstOn c (Fin.tail x) ∧ ∀ t, x 0 = Fin.tail x (c.emb k t) := by
  rw [constOn_iff_range, constOn_iff_range]
  constructor
  · intro h
    refine ⟨fun i a ha b hb => ?_, fun t => ?_⟩
    · have hi := h i
      by_cases hik : i = k
      · subst hik
        rw [range_extendMiddle_self] at hi
        exact hi _ (Set.mem_insert_of_mem _ ⟨a, ha, rfl⟩) _ (Set.mem_insert_of_mem _ ⟨b, hb, rfl⟩)
      · rw [range_extendMiddle_ne c k hik] at hi
        exact hi _ ⟨a, ha, rfl⟩ _ ⟨b, hb, rfl⟩
    · have hk := h k
      rw [range_extendMiddle_self] at hk
      exact hk _ (Set.mem_insert _ _) _ (Set.mem_insert_of_mem _ ⟨_, ⟨t, rfl⟩, rfl⟩)
  · rintro ⟨h1, h2⟩ i
    by_cases hik : i = k
    · rw [hik, range_extendMiddle_self]
      have h0 : ∀ a ∈ (insert 0 (Fin.succ '' Set.range (c.emb k)) : Set (Fin (m + 1))), x a = x 0 := by
        rintro a (rfl | ⟨_, ⟨u, rfl⟩, rfl⟩)
        · rfl
        · exact (h2 u).symm
      intro a ha b hb; rw [h0 a ha, h0 b hb]
    · rw [range_extendMiddle_ne c k hik]
      rintro _ ⟨a, ha, rfl⟩ _ ⟨b, hb, rfl⟩
      exact h1 i a ha b hb

theorem sum_block_count {m : ℕ} {β : Type*} [DecidableEq β] (c : OrderedFinpartition m) (x : Fin m → β)
    (hx : ConstOn c x) (v : β) :
    ∑ k, (if x (c.emb k ⟨0, c.partSize_pos k⟩) = v then (c.partSize k : ℤ) else 0) =
      ((univ.filter (fun j => x j = v)).card : ℤ) := by
  rw [card_filter, Nat.cast_sum]
  rw [← c.sum_sigma_eq_sum (fun j => ((if x j = v then 1 else 0 : ℕ) : ℤ))]
  apply sum_congr rfl
  intro k _
  have : ∀ t : Fin (c.partSize k), ((if x (c.emb k t) = v then 1 else 0 : ℕ) : ℤ) =
      if x (c.emb k ⟨0, c.partSize_pos k⟩) = v then 1 else 0 := by
    intro t; rw [hx k t ⟨0, c.partSize_pos k⟩]; split_ifs <;> simp
  rw [sum_congr rfl (fun t _ => this t), sum_const, card_univ, Fintype.card_fin]
  split_ifs <;> simp

open Classical in
/-- **Möbius inversion** on the set partitions of `Fin m`. -/
theorem mobius_injective {β : Type*} [DecidableEq β] : ∀ (m : ℕ) (x : Fin m → β),
    ∑ c : OrderedFinpartition m, (if ConstOn c x then mu c else 0) =
      if Function.Injective x then 1 else 0
  | 0, x => by
    rw [Fintype.sum_unique, if_pos (show ConstOn (default : OrderedFinpartition 0) x by
      intro i; exact Fin.elim0 i), if_pos (show Function.Injective x from fun i => Fin.elim0 i)]
    unfold mu
    simp [default_eq, atomic, mobF_one]
  | m + 1, x => by
    set x' : Fin m → β := Fin.tail x
    set N : ℤ := ((univ.filter (fun j => x' j = x 0)).card : ℤ)
    have hstep : ∀ c : OrderedFinpartition m,
        (if ConstOn c.extendLeft x then mu c.extendLeft else 0) +
          ∑ k, (if ConstOn (c.extendMiddle k) x then mu (c.extendMiddle k) else 0) =
        (if ConstOn c x' then mu c else 0) * (1 - N) := by
      intro c
      by_cases hc : ConstOn c x'
      · rw [if_pos ((constOn_extendLeft c x).mpr hc), mu_extendLeft, if_pos hc]
        have hk : ∀ k, (if ConstOn (c.extendMiddle k) x then mu (c.extendMiddle k) else 0) =
            -(if x' (c.emb k ⟨0, c.partSize_pos k⟩) = x 0 then (c.partSize k : ℤ) else 0) * mu c := by
          intro k
          rw [mu_extendMiddle]
          by_cases h0 : x' (c.emb k ⟨0, c.partSize_pos k⟩) = x 0
          · rw [if_pos ((constOn_extendMiddle c k x).mpr ⟨hc, fun t => by
              have := hc k t ⟨0, c.partSize_pos k⟩
              change x 0 = x' (c.emb k t)
              rw [this]; exact h0.symm⟩), if_pos h0]
          · rw [if_neg (fun h => h0 (((constOn_extendMiddle c k x).mp h).2 ⟨0, c.partSize_pos k⟩).symm),
              if_neg h0]
            ring
        rw [sum_congr rfl (fun k _ => hk k), ← sum_mul, sum_neg_distrib, sum_block_count c x' hc]
        ring
      · rw [if_neg (fun h => hc ((constOn_extendLeft c x).mp h)), if_neg hc, zero_mul, zero_add]
        apply sum_eq_zero
        intro k _
        rw [if_neg (fun h => hc ((constOn_extendMiddle c k x).mp h).1)]
    rw [← (extendEquiv m).sum_comp, Fintype.sum_sigma]
    have hstep' : ∀ c : OrderedFinpartition m,
        (∑ o : Option (Fin c.length), if ConstOn ((extendEquiv m) ⟨c, o⟩) x then
          mu ((extendEquiv m) ⟨c, o⟩) else 0) = (if ConstOn c x' then mu c else 0) * (1 - N) := by
      intro c
      rw [Fintype.sum_option]
      exact hstep c
    rw [sum_congr rfl (fun c _ => hstep' c), ← sum_mul, mobius_injective m x']
    -- `x` is injective iff `x'` is and `x 0` is not a value of `x'`
    have hx : x = Fin.cons (x 0) x' := (Fin.cons_self_tail x).symm
    have hinj : Function.Injective x ↔ x 0 ∉ Set.range x' ∧ Function.Injective x' := by
      conv_lhs => rw [hx]
      exact Fin.cons_injective_iff
    by_cases hi : Function.Injective x'
    · have hN : N ≤ 1 := by
        have : (univ.filter (fun j => x' j = x 0)).card ≤ 1 := by
          rw [card_le_one]; intro a ha b hb
          simp only [mem_filter] at ha hb
          exact hi (ha.2.trans hb.2.symm)
        unfold N; exact_mod_cast this
      by_cases hr : x 0 ∈ Set.range x'
      · obtain ⟨j, hj⟩ := hr
        have : 1 ≤ N := by
          unfold N
          have : 0 < (univ.filter (fun j => x' j = x 0)).card := card_pos.mpr ⟨j, by simp [hj]⟩
          exact_mod_cast this
        rw [if_pos hi, if_neg (fun h => (hinj.mp h).1 ⟨j, hj⟩)]
        have : N = 1 := le_antisymm hN this
        rw [this]; ring
      · have : N = 0 := by
          unfold N
          rw [Nat.cast_eq_zero, card_eq_zero, filter_eq_empty_iff]
          intro j _ hj; exact hr ⟨j, hj⟩
        rw [if_pos hi, if_pos (hinj.mpr ⟨hr, hi⟩), this]; ring
    · rw [if_neg hi, if_neg (fun h => hi (hinj.mp h).2)]; ring

end GradientKey.Concrete
