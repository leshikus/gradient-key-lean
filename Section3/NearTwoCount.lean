import NearTwoSets
import PairCount

/-!
# Counting the admissible pairs `Y`

For fixed `(j, b, c)`, the words `w` with bit `b` in row `j` that agree with `c` before `j` correspond to their
sets of deviations from `c` after `j`, the subsets of `T = {i : j < i}`. An admissible pair is a pair of distinct
words with disjoint deviation sets. So `2 · #Yset + 1 = 3^{|T|}` with `|T| = n - 1 - j`.
-/

noncomputable section


namespace GradientKey.Concrete

open Finset

variable {n : ℕ} (j : Fin n) (b : Bool) (c : ((univ : Finset (Fin n)).erase j) → Bool)

/-- Words with bit `b` in row `j` that agree with `c` before `j`. -/
def Uset : Finset (Word n) :=
  univ.filter (fun w : Word n => wbit w j = b ∧ ∀ i, i < j → wbit w i = cbit j c i)

/-- The rows after `j`. -/
def Tset : Finset (Fin n) := univ.filter (fun i : Fin n => j < i)

/-- The deviations of `w` from `c` after `j`. -/
def devSet (w : Word n) : Finset (Fin n) := (Tset j).filter (fun i => wbit w i ≠ cbit j c i)

/-- The word with bit `b` in row `j`, equal to `c` elsewhere except on `D`. -/
def wordOf (D : Finset (Fin n)) : Word n :=
  fun x => if x.1 = j then b else if x.1 ∈ D then !cbit j c x.1 else cbit j c x.1

theorem wbit_eq_of (w : Word n) (i : Fin n) : w ⟨i, mem_univ i⟩ = wbit w i := rfl

theorem word_ext {w w' : Word n} (h : ∀ i, wbit w i = wbit w' i) : w = w' := by
  funext x; exact h x.1

theorem devSet_injOn : Set.InjOn (devSet j c) (Uset j b c) := by
  intro w hw w' hw' he
  simp only [Uset, coe_filter, mem_univ, true_and, Set.mem_setOf_eq] at hw hw'
  apply word_ext
  intro i
  rcases lt_trichotomy i j with h | rfl | h
  · rw [hw.2 i h, hw'.2 i h]
  · rw [hw.1, hw'.1]
  · have := congrArg (fun D => i ∈ D) he
    simp only [devSet, Tset, mem_filter, mem_univ, true_and, h] at this
    cases h1 : wbit w i <;> cases h2 : wbit w' i <;> cases h3 : cbit j c i <;> simp_all

theorem wordOf_mem (D : Finset (Fin n)) (hD : D ⊆ Tset j) : wordOf j b c D ∈ Uset j b c := by
  unfold Uset
  rw [mem_filter]
  refine ⟨mem_univ _, by simp [wbit, wordOf], fun i hi => ?_⟩
  have hij : i ≠ j := ne_of_lt hi
  have hiD : i ∉ D := fun h => by
    have := hD h; simp [Tset] at this; exact absurd (lt_trans this hi) (lt_irrefl _)
  simp [wbit, wordOf, hij, hiD]

theorem devSet_wordOf (D : Finset (Fin n)) (hD : D ⊆ Tset j) : devSet j c (wordOf j b c D) = D := by
  ext i
  simp only [devSet, mem_filter, wordOf, wbit]
  constructor
  · rintro ⟨hT, hne⟩
    have hij : i ≠ j := by simp [Tset] at hT; exact ne_of_gt hT
    by_contra hiD
    simp [hij, hiD] at hne
  · intro hi
    have hT := hD hi
    have hij : i ≠ j := by simp [Tset] at hT; exact ne_of_gt hT
    refine ⟨hT, ?_⟩
    simp [hij, hi]

theorem devSet_image : (Uset j b c).image (devSet j c) = (Tset j).powerset := by
  ext D
  simp only [mem_image, mem_powerset]
  constructor
  · rintro ⟨w, -, rfl⟩; exact filter_subset _ _
  · intro hD; exact ⟨wordOf j b c D, wordOf_mem j b c D hD, devSet_wordOf j b c D hD⟩

theorem Yset_eq : Yset j b c = ((Uset j b c).powersetCard 2).filter
    (fun Y => ∀ y ∈ Y, ∀ z ∈ Y, y ≠ z → Disjoint (devSet j c y) (devSet j c z)) := by
  ext Y
  rw [mem_Yset, mem_filter, mem_powersetCard]
  constructor
  · rintro ⟨h2, hb, h1, h3⟩
    refine ⟨⟨fun y hy => ?_, h2⟩, fun y hy z hz hyz => ?_⟩
    · simp only [Uset, mem_filter, mem_univ, true_and]
      refine ⟨hb y hy, fun i hi => ?_⟩
      have := h1 i hi
      unfold dev at this
      rw [card_eq_zero, filter_eq_empty_iff] at this
      exact not_not.mp (this hy)
    · rw [disjoint_left]
      intro i hiy hiz
      simp only [devSet, Tset, mem_filter, mem_univ, true_and] at hiy hiz
      have := h3 i hiy.1
      unfold dev at this
      have : 1 < (Y.filter (fun w => wbit w i ≠ cbit j c i)).card :=
        one_lt_card.mpr ⟨y, mem_filter.mpr ⟨hy, hiy.2⟩, z, mem_filter.mpr ⟨hz, hiz.2⟩, hyz⟩
      omega
  · rintro ⟨⟨hU, h2⟩, hd⟩
    have hU' : ∀ y ∈ Y, wbit y j = b ∧ ∀ i, i < j → wbit y i = cbit j c i := fun y hy => by
      have := hU hy; simpa [Uset] using this
    refine ⟨h2, fun y hy => (hU' y hy).1, fun i hi => ?_, fun i hi => ?_⟩
    · unfold dev
      rw [card_eq_zero, filter_eq_empty_iff]
      intro y hy; exact not_not.mpr ((hU' y hy).2 i hi)
    · unfold dev
      by_contra hlt
      push_neg at hlt
      obtain ⟨y, hy, z, hz, hyz⟩ := one_lt_card.mp hlt
      simp only [mem_filter] at hy hz
      have := disjoint_left.mp (hd y hy.1 z hz.1 hyz)
      exact this (show i ∈ devSet j c y by simp [devSet, Tset, hi, hy.2])
        (show i ∈ devSet j c z by simp [devSet, Tset, hi, hz.2])

theorem card_Tset : (Tset j).card = n - 1 - j.val := by
  rw [← card_map Fin.valEmbedding]
  have : (Tset j).map Fin.valEmbedding = Finset.Ioo j.val n := by
    ext x; simp only [Tset, mem_map, mem_filter, mem_univ, true_and, Fin.valEmbedding_apply, mem_Ioo]
    constructor
    · rintro ⟨k, hk, rfl⟩; exact ⟨hk, k.2⟩
    · rintro ⟨h1, h2⟩; exact ⟨⟨x, h2⟩, h1, rfl⟩
  rw [this, Nat.card_Ioo]; omega

/-- `2 · #Yset + 1 = 3^{n - 1 - j}`. -/
theorem card_Yset : 2 * (Yset j b c).card + 1 = 3 ^ (n - 1 - j.val) := by
  rw [Yset_eq, two_mul_card_pairs _ (fun y z => Disjoint (devSet j c y) (devSet j c z))
    (fun a b h => h.symm), ← card_Tset, ← card_disjoint_pairs]
  -- the ordered pairs of words with disjoint deviation sets
  set U := Uset j b c
  set δ := devSet j c
  have hinj := devSet_injOn j b c
  have himg : ((U ×ˢ U).filter (fun p => Disjoint (δ p.1) (δ p.2))).image (Prod.map δ δ) =
      ((Tset j).powerset ×ˢ (Tset j).powerset).filter (fun p => Disjoint p.1 p.2) := by
    ext ⟨D1, D2⟩
    simp only [mem_image, mem_filter, mem_product, Prod.exists, Prod.map, Prod.mk.injEq]
    constructor
    · rintro ⟨y, z, ⟨⟨hy, hz⟩, hd⟩, rfl, rfl⟩
      rw [← devSet_image j b c]
      exact ⟨⟨mem_image_of_mem _ hy, mem_image_of_mem _ hz⟩, hd⟩
    · rintro ⟨⟨h1, h2⟩, hd⟩
      rw [← devSet_image j b c] at h1 h2
      obtain ⟨y, hy, rfl⟩ := mem_image.mp h1
      obtain ⟨z, hz, rfl⟩ := mem_image.mp h2
      exact ⟨y, z, ⟨⟨hy, hz⟩, hd⟩, rfl, rfl⟩
  have hcard : ((U ×ˢ U).filter (fun p => Disjoint (δ p.1) (δ p.2))).card =
      (((Tset j).powerset ×ˢ (Tset j).powerset).filter (fun p => Disjoint p.1 p.2)).card := by
    rw [← himg, card_image_of_injOn]
    intro p hp q hq he
    simp only [coe_filter, mem_product, Set.mem_setOf_eq] at hp hq
    simp only [Prod.map, Prod.mk.injEq] at he
    exact Prod.ext (hinj hp.1.1 hq.1.1 he.1) (hinj hp.1.2 hq.1.2 he.2)
  rw [← hcard]
  -- only the base word pairs with itself
  set w0 := wordOf j b c ∅
  have hw0 : w0 ∈ U := wordOf_mem j b c ∅ (empty_subset _)
  have hδ0 : δ w0 = ∅ := devSet_wordOf j b c ∅ (empty_subset _)
  have hsplit : (U ×ˢ U).filter (fun p => Disjoint (δ p.1) (δ p.2)) =
      insert (w0, w0) ((U ×ˢ U).filter (fun p => p.1 ≠ p.2 ∧ Disjoint (δ p.1) (δ p.2))) := by
    ext ⟨y, z⟩
    simp only [mem_filter, mem_product, mem_insert, Prod.mk.injEq]
    constructor
    · rintro ⟨⟨hy, hz⟩, hd⟩
      by_cases hyz : y = z
      · subst hyz
        left
        have : δ y = ∅ := disjoint_self.mp hd
        have := hinj hy hw0 (this.trans hδ0.symm)
        exact ⟨this, this⟩
      · right; exact ⟨⟨hy, hz⟩, hyz, hd⟩
    · rintro (⟨rfl, rfl⟩ | ⟨h, -, hd⟩)
      · exact ⟨⟨hw0, hw0⟩, by rw [hδ0]; exact disjoint_empty_left _⟩
      · exact ⟨h, hd⟩
  rw [hsplit, card_insert_of_notMem]
  simp

end GradientKey.Concrete
