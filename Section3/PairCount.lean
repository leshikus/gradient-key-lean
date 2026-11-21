import Mathlib

/-!
# Counting pairs

* `2 · #{2-subsets with a symmetric property} = #{ordered pairs of distinct elements with it}`;
* the ordered pairs of disjoint subsets of a set of `t` elements number `3^t`.
-/

namespace GradientKey.Concrete

open Finset

theorem two_mul_card_pairs {α : Type*} [DecidableEq α] (X : Finset α) (ρ : α → α → Prop)
    [DecidablePred fun Y : Finset α => ∀ y ∈ Y, ∀ z ∈ Y, y ≠ z → ρ y z]
    [DecidablePred fun p : α × α => p.1 ≠ p.2 ∧ ρ p.1 p.2] (hρ : ∀ a b, ρ a b → ρ b a) :
    2 * ((X.powersetCard 2).filter (fun Y => ∀ y ∈ Y, ∀ z ∈ Y, y ≠ z → ρ y z)).card =
      ((X ×ˢ X).filter (fun p => p.1 ≠ p.2 ∧ ρ p.1 p.2)).card := by
  classical
  set P := (X ×ˢ X).filter (fun p => p.1 ≠ p.2 ∧ ρ p.1 p.2)
  set Q := (X.powersetCard 2).filter (fun Y => ∀ y ∈ Y, ∀ z ∈ Y, y ≠ z → ρ y z)
  have hmaps : ∀ p ∈ P, ({p.1, p.2} : Finset α) ∈ Q := by
    intro p hp
    simp only [P, mem_filter, mem_product] at hp
    simp only [Q, mem_filter, mem_powersetCard]
    refine ⟨⟨?_, card_pair hp.2.1⟩, ?_⟩
    · intro x hx; simp only [mem_insert, mem_singleton] at hx; rcases hx with rfl | rfl
      · exact hp.1.1
      · exact hp.1.2
    · intro y hy z hz hyz
      simp only [mem_insert, mem_singleton] at hy hz
      rcases hy with rfl | rfl <;> rcases hz with rfl | rfl
      · exact absurd rfl hyz
      · exact hp.2.2
      · exact hρ _ _ hp.2.2
      · exact absurd rfl hyz
  rw [card_eq_sum_card_fiberwise hmaps, mul_comm, ← smul_eq_mul, ← sum_const]
  apply sum_congr rfl
  intro Y hY
  simp only [Q, mem_filter, mem_powersetCard] at hY
  obtain ⟨a, b, hab, rfl⟩ := card_eq_two.mp hY.1.2
  have : P.filter (fun p => ({p.1, p.2} : Finset α) = {a, b}) = {(a, b), (b, a)} := by
    ext ⟨x, y⟩
    simp only [P, mem_filter, mem_product, mem_insert, mem_singleton, Prod.mk.injEq]
    constructor
    · rintro ⟨-, he⟩
      have hx : x ∈ ({a, b} : Finset α) := he ▸ mem_insert_self x {y}
      have hy : y ∈ ({a, b} : Finset α) := he ▸ mem_insert_of_mem (mem_singleton_self y)
      simp only [mem_insert, mem_singleton] at hx hy
      rcases hx with rfl | rfl <;> rcases hy with rfl | rfl
      · have := congrArg Finset.card he; rw [card_pair hab] at this; simp at this
      · left; exact ⟨rfl, rfl⟩
      · right; exact ⟨rfl, rfl⟩
      · have := congrArg Finset.card he; rw [card_pair hab] at this; simp at this
    · have hs := hY.1.1
      have ha : a ∈ X := hs (mem_insert_self a {b})
      have hb : b ∈ X := hs (mem_insert_of_mem (mem_singleton_self b))
      have hr := hY.2 a (mem_insert_self a {b}) b (mem_insert_of_mem (mem_singleton_self b)) hab
      rintro (⟨rfl, rfl⟩ | ⟨rfl, rfl⟩)
      · exact ⟨⟨⟨ha, hb⟩, hab, hr⟩, rfl⟩
      · exact ⟨⟨⟨hb, ha⟩, Ne.symm hab, hρ _ _ hr⟩, pair_comm _ _⟩
  rw [this, card_pair]
  intro h; simp only [Prod.mk.injEq] at h; exact hab h.1

/-- Ordered pairs of disjoint subsets of `T`: `3^|T|`. -/
theorem card_disjoint_pairs {α : Type*} [DecidableEq α] (T : Finset α) :
    ((T.powerset ×ˢ T.powerset).filter (fun p => Disjoint p.1 p.2)).card = 3 ^ T.card := by
  rw [card_filter, sum_product]
  have : ∀ D ∈ T.powerset, (∑ D' ∈ T.powerset, if Disjoint D D' then 1 else 0) = 1 ^ D.card * 2 ^ (T.card - D.card) := by
    intro D hD
    rw [← card_filter, one_pow, one_mul]
    have : T.powerset.filter (fun D' => Disjoint D D') = (T \ D).powerset := by
      ext D'
      simp only [mem_filter, mem_powerset]
      constructor
      · rintro ⟨h1, h2⟩; exact subset_sdiff.mpr ⟨h1, h2.symm⟩
      · intro h; exact ⟨h.trans sdiff_subset, (subset_sdiff.mp h).2.symm⟩
    rw [this, card_powerset, card_sdiff_of_subset (mem_powerset.mp hD)]
  rw [sum_congr rfl this, sum_pow_mul_eq_add_pow]

end GradientKey.Concrete
