import BkInteger
import Counting

/-!
# Enumeration of the missing words: translation by `v ∈ {0,1}^n`

Section 3.3, enumeration of the missing words. Translating every column by `v`
(`w ↦ w ⊕ v`) negates the rows `i` with `v_i = 1`, so it keeps every row quality, the tree
and the total depth; it maps the set `R` of missing words to `R ⊕ v`. The map
`(R, w) ↦ (R ⊕ w, w)`, `w ∈ R`, is a bijection onto the pairs `(R', w)` with `0 ∈ R'`; each `R`
occurs in `r` pairs on the left and each `R'` in `2^n` pairs on the right. Hence the mean of the
total depth over the sets `R` of `r` missing words equals the mean over those with `0 ∈ R`
(`missing_mean_eq`). The depth of `R` is the total depth `D(A)` of any table `A` with missing
set `R` (`missingDepth_eq_table`), and `∑_A D(A) = m! ∑_R D(R)` (`sum_totalDepth_eq_missing`).
-/

noncomputable section

namespace GradientKey.Concrete

open Finset

variable {n m : ℕ}

/-- `v ⊕ w`. -/
def xorWord (v w : Word n) : Word n := fun i => Bool.xor (v i) (w i)

/-- The word `0`. -/
def zeroWord : Word n := fun _ => false

theorem xorWord_self (v : Word n) : xorWord v v = zeroWord := by
  funext i
  simp only [xorWord, zeroWord]
  cases v i <;> rfl

theorem xorWord_zero (v : Word n) : xorWord v zeroWord = v := by
  funext i
  simp only [xorWord, zeroWord]
  cases v i <;> rfl

theorem xorWord_involutive (v : Word n) : Function.Involutive (xorWord v) := by
  intro w
  funext i
  simp only [xorWord]
  cases v i <;> cases w i <;> rfl

/-- `w ↦ v ⊕ w` as an equivalence. -/
def xorEquiv (v : Word n) : Word n ≃ Word n where
  toFun := xorWord v
  invFun := xorWord v
  left_inv := xorWord_involutive v
  right_inv := xorWord_involutive v

/-- The table whose columns are those of `A` translated by `v`. -/
def translateTable (v : Word n) (A : Table n m) : Table n m :=
  fun i j => Bool.xor (v ⟨i, mem_univ i⟩) (A i j)

theorem translateTable_involutive (v : Word n) : Function.Involutive (translateTable (m := m) v) := by
  intro A
  funext i j
  simp only [translateTable]
  cases v ⟨i, mem_univ i⟩ <;> cases A i j <;> rfl

theorem translate_canon (hm : 0 < m) (v : Word n) (A : Table n m) :
    (List.ofFn (translateTable v A)).map (canon hm) = (List.ofFn A).map (canon hm) := by
  rw [List.map_ofFn, List.map_ofFn]
  congr 1
  funext i
  cases h : v ⟨i, mem_univ i⟩
  · have he : translateTable v A i = A i := by
      funext j
      simp [translateTable, h]
    simp only [Function.comp_apply, he]
  · have he : translateTable v A i = fun j => !(A i j) := by
      funext j
      simp [translateTable, h]
    simp only [Function.comp_apply, he, canon_not]

theorem translate_ldepth (hm : 0 < m) (v : Word n) (A : Table n m) :
    ldepth (List.ofFn (translateTable v A)) = ldepth (List.ofFn A) := by
  rw [← ldepth_map_canon hm (List.ofFn (translateTable v A)), translate_canon hm,
    ldepth_map_canon hm]

/-- Translation keeps the total depth. -/
theorem translate_totalDepth (hm : 0 < m) (hn : 0 < n) (v : Word n) (A : Table n m) :
    totalDepth (translateTable v A) hn univ = totalDepth A hn univ := by
  rw [totalDepth_eq_ldepth, totalDepth_eq_ldepth, translate_ldepth hm]

theorem translate_distinct (hm : 0 < m) (v : Word n) (A : Table n m) :
    DistinctColumns (translateTable v A) ↔ DistinctColumns A := by
  rw [← sep_iff_distinct, ← sep_iff_distinct,
    ← sep_map_canon hm (List.ofFn (translateTable v A)), translate_canon hm, sep_map_canon]

/-- Translation as an equivalence of `𝒜_{n,m}`. -/
def translateValid (hm : 0 < m) (v : Word n) : ValidTable n m ≃ ValidTable n m where
  toFun A := ⟨translateTable v A.1, (translate_distinct hm v A.1).mpr A.2⟩
  invFun A := ⟨translateTable v A.1, (translate_distinct hm v A.1).mpr A.2⟩
  left_inv A := Subtype.ext (translateTable_involutive v A.1)
  right_inv A := Subtype.ext (translateTable_involutive v A.1)

/-- `R ⊕ v`. -/
def translateSet (v : Word n) (R : Finset (Word n)) : Finset (Word n) :=
  R.map (xorEquiv v).toEmbedding

theorem mem_translateSet_iff (v w : Word n) (R : Finset (Word n)) :
    w ∈ translateSet v R ↔ xorWord v w ∈ R := by
  rw [translateSet, mem_map_equiv]
  rfl

theorem translateSet_card (v : Word n) (R : Finset (Word n)) :
    (translateSet v R).card = R.card := card_map _

theorem translateSet_involutive (v : Word n) : Function.Involutive (translateSet v) := by
  intro R
  ext w
  rw [mem_translateSet_iff, mem_translateSet_iff, xorWord_involutive]

theorem zero_mem_translate_iff (v : Word n) (R : Finset (Word n)) :
    zeroWord ∈ translateSet v R ↔ v ∈ R := by
  rw [mem_translateSet_iff, xorWord_zero]

open Classical in
/-- The missing set of the translated table is the translated missing set. -/
theorem translate_missing (v : Word n) (A : Table n m) :
    missing (translateTable v A) univ univ = translateSet v (missing A univ univ) := by
  have hp (j : Fin m) : pat (translateTable v A) univ j = xorWord v (pat A univ j) := by
    funext i
    rfl
  ext w
  rw [mem_translateSet_iff]
  simp only [missing, mem_sdiff, mem_univ, true_and, mem_image, hp]
  constructor
  · rintro h ⟨j, hj⟩
    exact h ⟨j, (congrArg (xorWord v) hj).trans (xorWord_involutive v w)⟩
  · rintro h ⟨j, hj⟩
    exact h ⟨j, (xorWord_involutive v (pat A univ j)).symm.trans (congrArg (xorWord v) hj)⟩

/-! ## The double count -/

open Classical in
/-- The sets of `r` words. -/
def missingSets (n r : ℕ) : Finset (Finset (Word n)) := univ.filter (fun R => R.card = r)

open Classical in
/-- The sets of `r` words that contain `0`. -/
def zeroSets (n r : ℕ) : Finset (Finset (Word n)) :=
  (missingSets n r).filter (fun R => zeroWord ∈ R)

open Classical in
/-- `r ∑_{|R|=r} f(R) = 2^n ∑_{|R|=r, 0∈R} f(R)` for `f` invariant under translation. -/
theorem missing_weighted_count (r : ℕ) (f : Finset (Word n) → ℝ)
    (hf : ∀ v R, f (translateSet v R) = f R) :
    (r : ℝ) * ∑ R ∈ missingSets n r, f R = (2 : ℝ) ^ n * ∑ R ∈ zeroSets n r, f R := by
  have hl : (r : ℝ) * ∑ R ∈ missingSets n r, f R =
      ∑ p ∈ (missingSets n r).sigma (σ := fun _ => Word n) (fun R => R), f p.1 := by
    rw [sum_sigma, mul_sum]
    refine sum_congr rfl fun R hR => ?_
    rw [sum_const, (mem_filter.mp hR).2, nsmul_eq_mul]
  have hr : (2 : ℝ) ^ n * ∑ R ∈ zeroSets n r, f R =
      ∑ p ∈ zeroSets n r ×ˢ (univ : Finset (Word n)), f p.1 := by
    rw [sum_product, mul_sum]
    refine sum_congr rfl fun R _ => ?_
    rw [sum_const, card_univ, card_word, nsmul_eq_mul]
    push_cast
    ring
  rw [hl, hr]
  refine sum_bij' (fun p _ => (translateSet p.2 p.1, p.2))
    (fun q _ => (⟨translateSet q.2 q.1, q.2⟩ : Σ _ : Finset (Word n), Word n)) ?_ ?_ ?_ ?_ ?_
  · rintro ⟨R, w⟩ h
    rw [mem_sigma] at h
    simp only [missingSets, zeroSets, mem_filter, mem_univ, true_and] at h
    simp only [mem_product, mem_univ, and_true, zeroSets, missingSets, mem_filter, true_and]
    exact ⟨(translateSet_card w R).trans h.1, (zero_mem_translate_iff w R).mpr h.2⟩
  · rintro ⟨R, w⟩ h
    simp only [mem_product, mem_univ, and_true, zeroSets, missingSets, mem_filter,
      true_and] at h
    rw [mem_sigma]
    simp only [missingSets, mem_filter, mem_univ, true_and]
    refine ⟨(translateSet_card w R).trans h.1, ?_⟩
    rw [← zero_mem_translate_iff, translateSet_involutive]
    exact h.2
  · rintro ⟨R, w⟩ _
    simp only [translateSet_involutive]
  · rintro ⟨R, w⟩ _
    simp only [translateSet_involutive]
  · rintro ⟨R, w⟩ _
    exact (hf w R).symm

open Classical in
/-- For `r > 0` and `f` invariant under translation, the mean of `f` over the sets of `r` words
equals its mean over those that contain `0`. -/
theorem missing_mean_eq_of_invariant (r : ℕ) (hr : 0 < r) (f : Finset (Word n) → ℝ)
    (hf : ∀ v R, f (translateSet v R) = f R) :
    (∑ R ∈ missingSets n r, f R) / (missingSets n r).card =
      (∑ R ∈ zeroSets n r, f R) / (zeroSets n r).card := by
  have hs := missing_weighted_count r f hf
  have hc := missing_weighted_count (n := n) r (fun _ => (1 : ℝ)) (fun _ _ => rfl)
  simp only [sum_const, nsmul_eq_mul, mul_one] at hc
  have hr' : (r : ℝ) ≠ 0 := by exact_mod_cast hr.ne'
  have hk : (2 : ℝ) ^ n / r ≠ 0 := div_ne_zero (by positivity) hr'
  have hx : ∑ R ∈ missingSets n r, f R = (2 : ℝ) ^ n / r * ∑ R ∈ zeroSets n r, f R := by
    rw [div_mul_eq_mul_div, eq_div_iff hr']
    linear_combination hs
  have ha : ((missingSets n r).card : ℝ) = (2 : ℝ) ^ n / r * (zeroSets n r).card := by
    rw [div_mul_eq_mul_div, eq_div_iff hr']
    linear_combination hc
  rw [hx, ha, mul_div_mul_left _ _ hk]

/-! ## The total depth of a set of missing words -/

open Classical in
/-- The total depth averaged over the `m!` tables with missing set `R`. -/
def missingDepth (n m : ℕ) (hn : 0 < n) (R : Finset (Word n)) : ℝ :=
  (∑ A : ValidTable n m, if missing A.1 univ univ = R then (totalDepth A.1 hn univ : ℝ) else 0) /
    (m.factorial : ℝ)

open Classical in
theorem missingDepth_translate (hm : 0 < m) (hn : 0 < n) (v : Word n) (R : Finset (Word n)) :
    missingDepth n m hn (translateSet v R) = missingDepth n m hn R := by
  unfold missingDepth
  congr 1
  refine Fintype.sum_equiv (translateValid hm v) _ _ fun A => ?_
  change _ = (if missing (translateTable v A.1) univ univ = R then
    (totalDepth (translateTable v A.1) hn univ : ℝ) else 0)
  rw [translate_missing, translate_totalDepth hm]
  by_cases h : missing A.1 univ univ = translateSet v R
  · rw [if_pos h, if_pos (by rw [h, translateSet_involutive])]
  · rw [if_neg h, if_neg (fun h' => h (by rw [← h', translateSet_involutive]))]

theorem ldepth_map_prow (π : Equiv.Perm (Fin m)) (L : List (Row m)) :
    ldepth (L.map (prow π)) = ldepth L := by
  rw [ldepth_eq_sum_cdep, ldepth_eq_sum_cdep]
  simp only [cdep_prow]
  exact π.sum_comp (cdep L)

open Classical in
/-- Two tables with the same missing set differ by a column permutation, so they have the same
total depth. -/
theorem totalDepth_eq_of_missing_eq (hn : 0 < n) (A B : ValidTable n m)
    (h : missing A.1 univ univ = missing B.1 univ univ) :
    totalDepth A.1 hn univ = totalDepth B.1 hn univ := by
  obtain ⟨T, hTA⟩ : ∃ T, univ.image (pat A.1 univ) = T := ⟨_, rfl⟩
  have hT : T.card = m := by
    rw [← hTA, card_image_of_injective _ (pat_univ_injective A.1 A.2), card_univ, Fintype.card_fin]
  have hTB : univ.image (pat B.1 univ) = T := by
    have h' := congrArg (fun S : Finset (Word n) => (univ : Finset (Word n)) \ S) h
    simp only [missing, sdiff_sdiff_eq_self (subset_univ _)] at h'
    rw [← hTA, h']
  let eA := imageEquiv T hT ⟨A, hTA⟩
  let eB := imageEquiv T hT ⟨B, hTB⟩
  let π : Equiv.Perm (Fin m) := eB.trans eA.symm
  have hp (j : Fin m) : pat A.1 univ (π j) = pat B.1 univ j := by
    change (eA (eA.symm (eB j))).val = (eB j).val
    rw [Equiv.apply_symm_apply]
  have hl : List.ofFn B.1 = (List.ofFn A.1).map (prow π) := by
    rw [List.map_ofFn]
    congr 1
    funext i j
    exact (congrFun (hp j) ⟨i, mem_univ i⟩).symm
  rw [totalDepth_eq_ldepth, totalDepth_eq_ldepth, hl, ldepth_map_prow]

theorem card_missing_univ (A : ValidTable n m) : (missing A.1 univ univ).card + m = 2 ^ n := by
  have hc := card_missing A.1 A.2 univ univ (fun _ _ _ _ i hi => absurd (mem_univ i) hi)
  simpa only [card_univ, Fintype.card_fin] using hc

open Classical in
/-- `missingDepth R` is the total depth of every table with missing set `R`. -/
theorem missingDepth_eq_table (hn : 0 < n) (R : Finset (Word n)) (A : ValidTable n m)
    (hA : missing A.1 univ univ = R) :
    missingDepth n m hn R = totalDepth A.1 hn univ := by
  have hR : R.card + m = 2 ^ n := hA ▸ card_missing_univ A
  unfold missingDepth
  rw [← sum_filter]
  have ht (B : ValidTable n m)
      (hB : B ∈ univ.filter (fun B : ValidTable n m => missing B.1 univ univ = R)) :
      (totalDepth B.1 hn univ : ℝ) = totalDepth A.1 hn univ := by
    exact_mod_cast totalDepth_eq_of_missing_eq hn B A ((mem_filter.mp hB).2.trans hA.symm)
  rw [sum_congr rfl ht, sum_const, card_missing_eq R hR, nsmul_eq_mul]
  have hf : (m.factorial : ℝ) ≠ 0 := by positivity
  field_simp

open Classical in
/-- `∑_{A ∈ 𝒜_{n,m}} D(A) = m! ∑_{|R| = r} D(R)` for `m + r = 2^n`. -/
theorem sum_totalDepth_eq_missing (hn : 0 < n) (r : ℕ) (hsize : m + r = 2 ^ n) :
    (∑ A : ValidTable n m, (totalDepth A.1 hn univ : ℝ)) =
      (m.factorial : ℝ) * ∑ R ∈ missingSets n r, missingDepth n m hn R := by
  have hf : (m.factorial : ℝ) ≠ 0 := by positivity
  have h1 (R : Finset (Word n)) : (m.factorial : ℝ) * missingDepth n m hn R =
      ∑ A : ValidTable n m, if missing A.1 univ univ = R then (totalDepth A.1 hn univ : ℝ) else 0 := by
    unfold missingDepth
    field_simp
  rw [mul_sum, sum_congr rfl (fun R _ => h1 R), sum_comm]
  refine sum_congr rfl fun A _ => ?_
  rw [sum_ite_eq, if_pos]
  simp only [missingSets, mem_filter, mem_univ, true_and]
  have := card_missing_univ A
  omega

open Classical in
/-- **Enumeration of the missing words.** For `m + r = 2^n`, `r ≥ 1`, the mean total depth over
the sets of `r` missing words equals the mean over the sets that contain `0`. -/
theorem missing_mean_eq (hn : 0 < n) (hm : 0 < m) (r : ℕ) (hr : 0 < r) :
    (∑ R ∈ missingSets n r, missingDepth n m hn R) / (missingSets n r).card =
      (∑ R ∈ zeroSets n r, missingDepth n m hn R) / (zeroSets n r).card :=
  missing_mean_eq_of_invariant r hr (missingDepth n m hn) (missingDepth_translate hm hn)

end GradientKey.Concrete
