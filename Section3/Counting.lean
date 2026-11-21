import Missing

/-!
# Tables as ordered sets of words

A table with distinct columns is an injective map `Fin m → {0,1}^n`. For a set `T` of `m` words exactly `m!`
tables have the columns `T`, and `|𝒜_{n,m}| = (2^n)_m`. The excess `t_{n,m}(G) - C(m)` is the mean over the
tables of `(D(A) - cdepth m) / m`, where `D(A) = ∑_j L_j`.
-/

noncomputable section

namespace GradientKey.Concrete

open Finset

variable {n m : ℕ}

/-- The words `{0,1}^n`, indexed by the rows `univ`. -/
abbrev Word (n : ℕ) := ↥(Finset.univ : Finset (Fin n)) → Bool

theorem pat_univ_injective (A : Table n m) (hA : DistinctColumns A) :
    Function.Injective (pat A univ) := by
  intro j k h
  apply hA
  funext r
  exact congrFun h ⟨r, mem_univ r⟩

/-- The table whose column `j` is the word `f j`. -/
def tableOf (f : Fin m → Word n) : Table n m := fun r j => f j ⟨r, mem_univ r⟩

theorem pat_tableOf (f : Fin m → Word n) : pat (tableOf f) univ = f := by
  funext j x; rfl

theorem tableOf_distinct (f : Fin m → Word n) (hf : Function.Injective f) :
    DistinctColumns (tableOf f) := by
  intro j k h
  apply hf
  funext x
  exact congrFun h x.1

/-- `𝒜_{n,m}` is the set of injective maps `Fin m → {0,1}^n`. -/
def validEquiv : ValidTable n m ≃ (Fin m ↪ Word n) where
  toFun A := ⟨pat A.1 univ, pat_univ_injective A.1 A.2⟩
  invFun f := ⟨tableOf f, tableOf_distinct f f.injective⟩
  left_inv A := by apply Subtype.ext; funext r j; rfl
  right_inv f := by ext j x; rfl

theorem card_word : Fintype.card (Word n) = 2 ^ n := by
  rw [Fintype.card_fun, Fintype.card_coe, card_univ, Fintype.card_fin, Fintype.card_bool]

theorem card_valid : Fintype.card (ValidTable n m) = (2 ^ n).descFactorial m := by
  rw [Fintype.card_congr validEquiv, Fintype.card_embedding_eq, card_word, Fintype.card_fin]

/-- The tables with the set of columns `T` correspond to the bijections `Fin m ≃ T`. -/
def imageEquiv (T : Finset (Word n)) (hT : T.card = m) :
    {A : ValidTable n m // univ.image (pat A.1 univ) = T} ≃ (Fin m ≃ T) where
  toFun A := Equiv.ofBijective
    (fun j => ⟨pat A.1.1 univ j, A.2.subst (motive := fun T' => pat A.1.1 univ j ∈ T') (mem_image_of_mem _ (mem_univ j))⟩)
    ((Fintype.bijective_iff_injective_and_card _).mpr
      ⟨fun j k h => pat_univ_injective A.1.1 A.1.2 (congrArg Subtype.val h),
        by rw [Fintype.card_fin, Fintype.card_coe, hT]⟩)
  invFun e := ⟨⟨tableOf (fun j => (e j).1),
      tableOf_distinct _ (fun j k h => e.injective (Subtype.ext h))⟩, by
    ext p
    rw [pat_tableOf]
    simp only [mem_image, mem_univ, true_and]
    constructor
    · rintro ⟨j, rfl⟩; exact (e j).2
    · intro hp; exact ⟨e.symm ⟨p, hp⟩, by simp⟩⟩
  left_inv A := by apply Subtype.ext; apply Subtype.ext; funext r j; rfl
  right_inv e := by ext j; rfl

theorem card_image_eq (T : Finset (Word n)) (hT : T.card = m) :
    (univ.filter (fun A : ValidTable n m => univ.image (pat A.1 univ) = T)).card = m.factorial := by
  rw [← Fintype.card_subtype, Fintype.card_congr (imageEquiv T hT)]
  have e : Fin m ≃ T := (Fintype.equivFinOfCardEq (by rw [Fintype.card_coe, hT])).symm
  rw [Fintype.card_equiv e, Fintype.card_fin]

/-- Exactly `m!` tables miss a given set `B` of `2^n - m` words. -/
theorem card_missing_eq (B : Finset (Word n)) (hB : B.card + m = 2 ^ n) :
    (univ.filter (fun A : ValidTable n m => missing A.1 univ univ = B)).card = m.factorial := by
  have hT : (univ \ B).card = m := by
    rw [card_sdiff_of_subset (subset_univ _), card_univ, card_word]; omega
  rw [← card_image_eq (univ \ B) hT]
  congr 1
  apply Finset.filter_congr
  intro A _
  unfold missing
  constructor
  · rintro rfl; exact (Finset.sdiff_sdiff_eq_self (subset_univ _)).symm
  · intro h; rw [h]; exact Finset.sdiff_sdiff_eq_self (subset_univ _)

theorem cdepth_div (hm : 0 < m) : (cdepth m : ℝ) / m = completeCost m := by
  unfold cdepth completeCost
  have hl : 2 ^ Nat.log 2 m ≤ m := Nat.pow_log_le_self 2 (by omega)
  have hle : 2 ^ (Nat.log 2 m + 1) ≤ m * (Nat.log 2 m + 2) := by
    calc 2 ^ (Nat.log 2 m + 1) = 2 * 2 ^ Nat.log 2 m := by ring
      _ ≤ 2 * m := by omega
      _ ≤ m * (Nat.log 2 m + 2) := by nlinarith
  rw [Nat.cast_sub hle]
  have hm' : (m : ℝ) ≠ 0 := by exact_mod_cast hm.ne'
  push_cast
  field_simp

/-- `t_{n,m}(G) - C(m) = ∑_A (D(A) - cdepth m) / (m |𝒜_{n,m}|)`. -/
theorem tG_sub_completeCost (hn : 0 < n) (hm : 2 ≤ m) (hsize : m ≤ 2 ^ n) :
    tG n m hn - completeCost m =
      (∑ A : ValidTable n m, ((totalDepth A.1 hn univ : ℝ) - cdepth m)) /
        ((m : ℝ) * Fintype.card (ValidTable n m)) := by
  have hne : Nonempty (Sample n m) := sample_nonempty hm hsize
  have hpos : 0 < Fintype.card (ValidTable n m) :=
    Fintype.card_pos_iff.mpr ⟨(Classical.arbitrary (Sample n m)).1⟩
  have hV : (Fintype.card (ValidTable n m) : ℝ) ≠ 0 := by exact_mod_cast hpos.ne'
  have hm' : (m : ℝ) ≠ 0 := by exact_mod_cast (show m ≠ 0 by omega)
  rw [← cdepth_div (by omega)]
  unfold tG cost
  have hc : ∀ A : ValidTable n m, (∑ j : Fin m, (leafDepth A.1 hn j : ℝ)) = totalDepth A.1 hn univ := by
    intro A; rw [← Nat.cast_sum, sum_leafDepth_eq_totalDepth A.1 A.2 hn]
  simp only [hc]
  rw [Finset.sum_sub_distrib, Finset.sum_const, Finset.card_univ, nsmul_eq_mul, ← Finset.sum_div]
  field_simp

end GradientKey.Concrete
