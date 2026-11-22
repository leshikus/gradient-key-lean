import Dense

/-!
# Missing words of a candidate set

The columns of a candidate set `S` agree outside a set `F` of rows. Their patterns on `F` are distinct words of
`{0,1}^F`; the other words are the *missing words* `missing A F S`. This file relates the missing words to the
sizes of the children, and proves that `|F| + 1` missing words of which every row separates at most one form a
ball of radius `1`.
-/

noncomputable section

namespace GradientKey.Concrete

open Finset

variable {n m : ℕ}

/-- The missing words of `S` on the rows `F`. -/
def missing (A : Table n m) (F : Finset (Fin n)) (S : Finset (Fin m)) : Finset (F → Bool) :=
  univ \ S.image (pat A F)

theorem card_univ_pat (F : Finset (Fin n)) : (univ : Finset (F → Bool)).card = 2 ^ F.card := by
  rw [card_univ, Fintype.card_fun, Fintype.card_coe, Fintype.card_bool]

theorem card_missing (A : Table n m) (hA : DistinctColumns A) (F : Finset (Fin n))
    (S : Finset (Fin m)) (hS : AgreeOff A F S) : (missing A F S).card + S.card = 2 ^ F.card := by
  unfold missing
  rw [card_sdiff_of_subset (subset_univ _), card_image_of_injOn (pat_injOn A hA F S hS),
    card_univ_pat]
  have := card_le_two_pow A hA F S hS
  omega

/-- Half of the words of `{0,1}^F` have bit `b` at `x`. -/
theorem card_half (F : Finset (Fin n)) (x : F) (b : Bool) :
    ((univ : Finset (F → Bool)).filter (fun p => p x = b)).card = 2 ^ (F.card - 1) := by
  classical
  have hle : ∀ b', ((univ : Finset (F → Bool)).filter (fun p => p x = b')).card ≤ 2 ^ (F.card - 1) := by
    intro b'
    let f : (F → Bool) → ((F.erase x.1) → Bool) := fun p y => p ⟨y.1, mem_of_mem_erase y.2⟩
    have hinj : Set.InjOn f ((univ : Finset (F → Bool)).filter (fun p => p x = b')) := by
      intro p hp q hq he
      simp only [coe_filter, mem_univ, true_and, Set.mem_setOf_eq] at hp hq
      funext y
      by_cases hy : y = x
      · subst hy; rw [hp, hq]
      · have := congrFun he ⟨y.1, mem_erase.mpr ⟨fun h => hy (Subtype.ext h), y.2⟩⟩
        simpa [f] using this
    have := card_le_card_of_injOn f (t := univ) (fun _ _ => mem_univ _) hinj
    rwa [card_univ, Fintype.card_fun, Fintype.card_coe, card_erase_of_mem x.2,
      Fintype.card_bool] at this
  have hsum := card_filter_add_card_filter_not (s := (univ : Finset (F → Bool))) (fun p => p x = true)
  rw [card_univ_pat] at hsum
  have hF : 1 ≤ F.card := card_pos.mpr ⟨x.1, x.2⟩
  have hpow : 2 ^ F.card = 2 * 2 ^ (F.card - 1) := by
    rw [← pow_succ']; congr 1; omega
  have h1 := hle true
  have h0 := hle false
  have e : (univ.filter fun p : F → Bool => ¬p x = true) = univ.filter (fun p => p x = false) := by
    ext p; simp
  rw [e] at hsum
  cases b <;> omega

/-- `|S_b| + r_b = 2^{k-1}`: the child on side `b` of row `c` and the missing words on that side. -/
theorem slice_add_missing (A : Table n m) (hA : DistinctColumns A) (F : Finset (Fin n))
    (S : Finset (Fin m)) (hS : AgreeOff A F S) (c : Fin n) (hc : c ∈ F) (b : Bool) :
    (slice A S c b).card + ((missing A F S).filter (fun p => p ⟨c, hc⟩ = b)).card =
      2 ^ (F.card - 1) := by
  classical
  rw [← card_half F ⟨c, hc⟩ b]
  have himg : (S.image (pat A F)).filter (fun p => p ⟨c, hc⟩ = b) = (slice A S c b).image (pat A F) := by
    rw [filter_image]; rfl
  have hcard : ((S.image (pat A F)).filter (fun p => p ⟨c, hc⟩ = b)).card = (slice A S c b).card := by
    rw [himg, card_image_of_injOn]
    exact (pat_injOn A hA F S hS).mono (by intro j hj; simp only [slice, coe_filter] at hj; exact hj.1)
  rw [← hcard]
  unfold missing
  have he : (univ \ S.image (pat A F)).filter (fun p => p ⟨c, hc⟩ = b) =
      (univ.filter fun p : F → Bool => p ⟨c, hc⟩ = b) \
        (S.image (pat A F)).filter (fun p => p ⟨c, hc⟩ = b) := by
    ext p; simp only [mem_filter, mem_sdiff, mem_univ, true_and]; tauto
  have hsub : (S.image (pat A F)).filter (fun p => p ⟨c, hc⟩ = b) ⊆
      univ.filter fun p : F → Bool => p ⟨c, hc⟩ = b := filter_subset_filter _ (subset_univ _)
  rw [he, card_sdiff_of_subset hsub]
  have := card_le_card hsub
  omega

section Ball

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- The word `c` with bit `x` flipped. -/
def flipAt (c : ι → Bool) (x : ι) : ι → Bool := Function.update c x (!c x)

/-- The ball of radius `1` around `c`. -/
def ball (c : ι → Bool) : Finset (ι → Bool) := insert c (univ.image (flipAt c))

theorem flipAt_self (c : ι → Bool) (x : ι) : flipAt c x x = !c x := by simp [flipAt]

theorem flipAt_ne (c : ι → Bool) {x y : ι} (h : y ≠ x) : flipAt c x y = c y := by
  simp [flipAt, Function.update_of_ne h]

theorem flipAt_injective (c : ι → Bool) : Function.Injective (flipAt c) := by
  intro x y h
  by_contra hxy
  have := congrFun h x
  rw [flipAt_self, flipAt_ne c hxy] at this
  cases hc : c x <;> simp [hc] at this

theorem flipAt_ne_self (c : ι → Bool) (x : ι) : flipAt c x ≠ c := by
  intro h
  have := congrFun h x
  rw [flipAt_self] at this
  cases hc : c x <;> simp [hc] at this

theorem card_ball (c : ι → Bool) : (ball c).card = Fintype.card ι + 1 := by
  unfold ball
  rw [card_insert_of_notMem, card_image_of_injective _ (flipAt_injective c), card_univ]
  simp only [mem_image, mem_univ, true_and, not_exists]
  exact fun x => flipAt_ne_self c x

theorem mem_ball (c p : ι → Bool) : p ∈ ball c ↔ p = c ∨ ∃ x, p = flipAt c x := by
  unfold ball
  simp only [mem_insert, mem_image, mem_univ, true_and]
  constructor
  · rintro (h | ⟨x, hx⟩)
    · exact Or.inl h
    · exact Or.inr ⟨x, hx.symm⟩
  · rintro (h | ⟨x, hx⟩)
    · exact Or.inl h
    · exact Or.inr ⟨x, hx.symm⟩

/-- In a ball, exactly one word has bit `!c x` at `x`. -/
theorem ball_filter_flip (c : ι → Bool) (x : ι) :
    (ball c).filter (fun p => p x = !c x) = {flipAt c x} := by
  ext p
  simp only [mem_filter, mem_ball, mem_singleton]
  constructor
  · rintro ⟨h | ⟨y, rfl⟩, hp⟩
    · subst h; cases hc : p x <;> simp [hc] at hp
    · by_cases hyx : y = x
      · rw [hyx]
      · rw [flipAt_ne c (Ne.symm hyx)] at hp; cases hc : c x <;> simp [hc] at hp
  · rintro rfl
    exact ⟨Or.inr ⟨x, rfl⟩, flipAt_self c x⟩

theorem ball_filter_same (c : ι → Bool) (x : ι) :
    ((ball c).filter (fun p => p x = c x)).card = Fintype.card ι := by
  have h := card_filter_add_card_filter_not (s := ball c) (fun p => p x = c x)
  have e : (ball c).filter (fun p => ¬p x = c x) = (ball c).filter (fun p => p x = !c x) := by
    congr 1; ext p; cases p x <;> cases c x <;> simp
  rw [e, ball_filter_flip, card_singleton, card_ball] at h
  omega

/-- `|ι| + 1` words of which every coordinate separates at most one from the others form a ball. -/
theorem isBall_of_sep (M : Finset (ι → Bool)) (hM : M.card = Fintype.card ι + 1)
    (hsep : ∀ x, (M.filter (fun p => p x = true)).card ≤ 1 ∨
      (M.filter (fun p => p x = false)).card ≤ 1) : ∃ c, M = ball c := by
  classical
  -- the word of majority bits
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
  have hcM : c ∈ M := by
    by_contra hc
    have : ∑ p ∈ M, 1 ≤ ∑ p ∈ M, (D p).card :=
      sum_le_sum (fun p hp => hpos p (fun h => hc (h ▸ hp)))
    simp at this
    omega
  have hsum' : ∑ p ∈ M.erase c, (D p).card ≤ Fintype.card ι := by
    have := sum_erase_add M (fun p => (D p).card) hcM
    omega
  have hone : ∀ p ∈ M.erase c, (D p).card = 1 := by
    by_contra h
    push_neg at h
    obtain ⟨q, hq, hq1⟩ := h
    have hlt : ∑ p ∈ M.erase c, 1 < ∑ p ∈ M.erase c, (D p).card := by
      apply sum_lt_sum
      · intro p hp; exact hpos p (ne_of_mem_erase hp)
      · exact ⟨q, hq, by have := hpos q (ne_of_mem_erase hq); omega⟩
    rw [sum_const, card_erase_of_mem hcM, hM, smul_eq_mul, mul_one] at hlt
    omega
  refine ⟨c, ?_⟩
  have hsub : M.erase c ⊆ univ.image (flipAt c) := by
    intro p hp
    obtain ⟨x, hx⟩ := card_eq_one.mp (hone p hp)
    have hxD : x ∈ D p := by rw [hx]; exact mem_singleton_self x
    simp only [D, mem_filter, mem_univ, true_and] at hxD
    refine mem_image.mpr ⟨x, mem_univ _, ?_⟩
    funext y
    by_cases hyx : y = x
    · subst hyx; rw [flipAt_self]; cases hp' : p y <;> cases hc' : c y <;> simp_all
    · rw [flipAt_ne c hyx]
      by_contra hne
      have : y ∈ D p := by simp [D, Ne.symm hne, hne]
      rw [hx, mem_singleton] at this
      exact hyx this
  have heq : M.erase c = univ.image (flipAt c) := by
    apply eq_of_subset_of_card_le hsub
    rw [card_image_of_injective _ (flipAt_injective c), card_univ, card_erase_of_mem hcM, hM]
    omega
  unfold ball
  rw [← heq, insert_erase hcM]

theorem ball_injective (hι : 2 ≤ Fintype.card ι) : Function.Injective (ball (ι := ι)) := by
  intro c c' h
  by_contra hne
  have hc : c ∈ ball c' := h ▸ (mem_ball c c).mpr (Or.inl rfl)
  rcases (mem_ball c' c).mp hc with h1 | ⟨x, hx⟩
  · exact hne h1
  obtain ⟨y, hyx⟩ : ∃ y, y ≠ x := by
    by_contra hy; push_neg at hy
    have : Fintype.card ι ≤ 1 := Fintype.card_le_one_iff.mpr (fun a b => (hy a).trans (hy b).symm)
    omega
  have hm : flipAt c y ∈ ball c' := h ▸ (mem_ball c _).mpr (Or.inr ⟨y, rfl⟩)
  rcases (mem_ball c' _).mp hm with h2 | ⟨z, hz⟩
  · have := congrFun h2 x
    rw [flipAt_ne c (Ne.symm hyx), hx, flipAt_self] at this
    cases hc : c' x <;> simp [hc] at this
  · -- `flipAt c y` differs from `c'` at `x` and at `y`
    have ex := congrFun hz x
    have ey := congrFun hz y
    rw [flipAt_ne c (Ne.symm hyx), hx, flipAt_self] at ex
    rw [flipAt_self, hx, flipAt_ne c' hyx] at ey
    by_cases hzx : z = x
    · subst hzx; rw [flipAt_ne c' hyx] at ey; cases hc : c' y <;> simp [hc] at ey
    · rw [flipAt_ne c' (Ne.symm hzx)] at ex; cases hc : c' x <;> simp [hc] at ex

end Ball

section Child

/-- Extend a word on `F \ {g}` by the bit `b` at `g`. -/
def extB (F : Finset (Fin n)) (g : Fin n) (q : (F.erase g) → Bool) (b : Bool) : F → Bool :=
  fun x => if h : x.1 = g then b else q ⟨x.1, mem_erase.mpr ⟨h, x.2⟩⟩

/-- Restrict a word on `F` to `F \ {g}`. -/
def resW (F : Finset (Fin n)) (g : Fin n) (c : F → Bool) : (F.erase g) → Bool :=
  fun y => c ⟨y.1, mem_of_mem_erase y.2⟩

theorem extB_eq_iff (F : Finset (Fin n)) (g : Fin n) (hg : g ∈ F) (q : (F.erase g) → Bool) (b : Bool)
    (p : F → Bool) : extB F g q b = p ↔ p ⟨g, hg⟩ = b ∧ q = resW F g p := by
  constructor
  · rintro rfl
    refine ⟨by simp [extB], ?_⟩
    funext y
    have hy : y.1 ≠ g := (mem_erase.mp y.2).1
    simp [resW, extB, hy]
  · rintro ⟨h1, rfl⟩
    funext x
    by_cases hx : x.1 = g
    · have : x = ⟨g, hg⟩ := Subtype.ext hx
      subst this; simp [extB, h1]
    · simp [extB, resW, hx]

theorem resW_flipAt (F : Finset (Fin n)) (g : Fin n) (c : F → Bool) (x : F) (hx : x.1 ≠ g) :
    resW F g (flipAt c x) = flipAt (resW F g c) ⟨x.1, mem_erase.mpr ⟨hx, x.2⟩⟩ := by
  funext y
  by_cases hyx : y.1 = x.1
  · have e1 : (⟨y.1, mem_of_mem_erase y.2⟩ : F) = x := Subtype.ext hyx
    have e2 : y = ⟨x.1, mem_erase.mpr ⟨hx, x.2⟩⟩ := Subtype.ext hyx
    simp only [resW]
    rw [e1, e2, flipAt_self, flipAt_self]
    rfl
  · have e1 : (⟨y.1, mem_of_mem_erase y.2⟩ : F) ≠ x := fun h => hyx (congrArg Subtype.val h)
    have e2 : y ≠ ⟨x.1, mem_erase.mpr ⟨hx, x.2⟩⟩ := fun h => hyx (congrArg Subtype.val h)
    simp only [resW]
    rw [flipAt_ne c e1, flipAt_ne _ e2]
    rfl

theorem agreeOff_slice (A : Table n m) (F : Finset (Fin n)) (S : Finset (Fin m))
    (hS : AgreeOff A F S) (g : Fin n) (b : Bool) : AgreeOff A (F.erase g) (slice A S g b) := by
  intro j1 h1 j2 h2 r hr
  simp only [slice, mem_filter] at h1 h2
  by_cases hrg : r = g
  · subst hrg; rw [h1.2, h2.2]
  · exact hS j1 h1.1 j2 h2.1 r (fun hrF => hr (mem_erase.mpr ⟨hrg, hrF⟩))

theorem mem_missing_slice (A : Table n m) (F : Finset (Fin n)) (S : Finset (Fin m)) (g : Fin n)
    (hg : g ∈ F) (b : Bool) (q : (F.erase g) → Bool) :
    q ∈ missing A (F.erase g) (slice A S g b) ↔ extB F g q b ∈ missing A F S := by
  have key : ∀ j, (A g j = b ∧ pat A (F.erase g) j = q) ↔ pat A F j = extB F g q b := by
    intro j
    rw [show pat A F j = extB F g q b ↔ extB F g q b = pat A F j from eq_comm,
      extB_eq_iff F g hg q b]
    constructor
    · rintro ⟨h1, rfl⟩; exact ⟨h1, rfl⟩
    · rintro ⟨h1, h2⟩; exact ⟨h1, h2.symm⟩
  unfold missing
  simp only [mem_sdiff, mem_univ, true_and, mem_image, slice, mem_filter, not_exists, not_and]
  constructor
  · intro h j hj he
    obtain ⟨h1, h2⟩ := (key j).mpr he
    exact h j ⟨hj, h1⟩ h2
  · intro h j hj he
    exact h j hj.1 ((key j).mp ⟨hj.2, he⟩)

/-- If the missing words form a ball around `c`, those on the side `c_g` of row `g` form a ball
around the restriction of `c`. -/
theorem missing_slice_ball (A : Table n m) (F : Finset (Fin n)) (S : Finset (Fin m)) (g : Fin n)
    (hg : g ∈ F) (c : F → Bool) (hM : missing A F S = ball c) :
    missing A (F.erase g) (slice A S g (c ⟨g, hg⟩)) = ball (resW F g c) := by
  ext q
  rw [mem_missing_slice A F S g hg, hM, mem_ball, mem_ball]
  constructor
  · rintro (h | ⟨x, hx⟩)
    · exact Or.inl ((extB_eq_iff F g hg q _ c).mp h).2
    · obtain ⟨h1, h2⟩ := (extB_eq_iff F g hg q _ _).mp hx
      have hxg : x.1 ≠ g := by
        intro hxg
        have : x = ⟨g, hg⟩ := Subtype.ext hxg
        subst this
        rw [flipAt_self] at h1
        cases hc : c ⟨g, hg⟩ <;> simp [hc] at h1
      right
      exact ⟨_, h2.trans (resW_flipAt F g c x hxg)⟩
  · rintro (h | ⟨y, hy⟩)
    · exact Or.inl ((extB_eq_iff F g hg q _ c).mpr ⟨rfl, h⟩)
    · right
      have hyg : y.1 ≠ g := (mem_erase.mp y.2).1
      let x : F := ⟨y.1, mem_of_mem_erase y.2⟩
      refine ⟨x, (extB_eq_iff F g hg q _ _).mpr ⟨?_, ?_⟩⟩
      · exact flipAt_ne c (fun h => hyg (congrArg Subtype.val h).symm)
      · rw [resW_flipAt F g c x hyg]; exact hy

end Child

end GradientKey.Concrete
