import FirstsCount
import Counting

/-!
# Proposition 3.3 (`prop:small-m`)

A *type* is a row up to complement; we take the representative with a `0` in column `0`. There are
`M = 2^{m-1}` types. `B_k` is the sum of `L̄ - C(m)` over the ordered `k`-tuples of distinct types that separate
the columns, the cost being that of the tree `G` builds from the rows in this order. Then, for `2 ≤ m ≤ 2^n`,
`t_{n,m}(G) - C(m) = N_m(n) / (2^n)_m` with `N_m(n) = ∑_{j=1}^M a_j (2j)^n` and
`a_j = ∑_{k ≥ j} (-1)^{k-j} C(k,j) B_k / k!`.
-/

noncomputable section

open Classical

namespace GradientKey.Concrete

open Finset

variable {n m : ℕ}

/-- Types: rows with a `0` in column `0`. -/
abbrev Ty (m : ℕ) (hm : 0 < m) := {r : Row m // r ⟨0, hm⟩ = false}

/-- `D(L) - cdepth m` if the rows of `L` separate the columns, else `0`. -/
def excessL (m : ℕ) (L : List (Row m)) : ℤ := if Sep L then (ldepth L : ℤ) - cdepth m else 0

/-- The same for a list of types. -/
def excessT (hm : 0 < m) (t : List (Ty m hm)) : ℤ := excessL m (t.map Subtype.val)

/-- `m B_k`: the sum of `D - cdepth m` over the ordered `k`-tuples of distinct types. -/
def Bint (hm : 0 < m) (k : ℕ) : ℤ := embSum (excessT hm) k

/-- `B_k`: the sum of `L̄ - C(m)` over the ordered `k`-tuples of distinct types. -/
def Bk (hm : 0 < m) (k : ℕ) : ℝ := (Bint hm k : ℝ) / m

/-- `M`, the number of types. -/
def numTypes (hm : 0 < m) : ℕ := Fintype.card (Ty m hm)

/-- `a_j = ∑_{k ≥ j} (-1)^(k-j) C(k,j) B_k / k!`. -/
def coeffA (hm : 0 < m) (j : ℕ) : ℝ :=
  ∑ k ∈ range (numTypes hm + 1), (-1 : ℝ) ^ (k - j) * (k.choose j : ℝ) * Bk hm k / k.factorial

/-- `N_m(n) = ∑_{j=1}^M a_j (2j)^n`. -/
def numer (hm : 0 < m) (n : ℕ) : ℝ := ∑ j ∈ Icc 1 (numTypes hm), coeffA hm j * (2 * j : ℝ) ^ n

theorem excessL_canon (hm : 0 < m) (L : List (Row m)) : excessL m (L.map (canon hm)) = excessL m L := by
  unfold excessL
  rw [ldepth_map_canon]
  by_cases h : Sep L
  · rw [if_pos ((sep_map_canon hm L).mpr h), if_pos h]
  · rw [if_neg (fun h' => h ((sep_map_canon hm L).mp h')), if_neg h]

theorem excessL_firsts (L : List (Row m)) : excessL m (firsts L) = excessL m L := by
  unfold excessL
  rw [ldepth_firsts]
  by_cases h : Sep L
  · rw [if_pos ((sep_firsts L).mpr h), if_pos h]
  · rw [if_neg (fun h' => h ((sep_firsts L).mp h')), if_neg h]

theorem map_firsts {α β : Type*} [DecidableEq α] [DecidableEq β] (f : α → β) (hf : Function.Injective f)
    (l : List α) : (firsts l).map f = firsts (l.map f) := by
  induction l using List.reverseRecOn with
  | nil => rfl
  | append_singleton l a ih =>
    rw [List.map_append, List.map_singleton, firsts_concat, firsts_concat, ← ih]
    have : f a ∈ (firsts l).map f ↔ a ∈ firsts l := by
      rw [List.mem_map]
      exact ⟨fun ⟨b, hb, he⟩ => hf he ▸ hb, fun h => ⟨a, h, rfl⟩⟩
    by_cases h : a ∈ firsts l
    · rw [if_pos h, if_pos (this.mpr h)]
    · rw [if_neg h, if_neg (fun h' => h (this.mp h')), List.map_append]; rfl

theorem excessT_firsts (hm : 0 < m) (t : List (Ty m hm)) : excessT hm (firsts t) = excessT hm t := by
  unfold excessT
  rw [map_firsts _ Subtype.val_injective, excessL_firsts]

/-- A table is a sequence of types and a sequence of orientations. -/
def rowsEquiv (hm : 0 < m) : Table n m ≃ (Fin n → Ty m hm) × (Fin n → Bool) where
  toFun A := (fun r => ⟨canon hm (A r), canon_zero hm (A r)⟩, fun r => A r ⟨0, hm⟩)
  invFun p := fun r k => if p.2 r then !(p.1 r).1 k else (p.1 r).1 k
  left_inv A := by
    funext r k
    simp only [canon]
    split_ifs with h <;> simp
  right_inv p := by
    obtain ⟨τ, o⟩ := p
    ext r k
    · simp only [canon, (τ r).2]
      cases o r <;> simp
    · simp only [(τ r).2]; cases o r <;> simp

/-- The numerator identity: `∑_A (D(A) - cdepth m) = 2^n ∑_k S(n,k) m B_k`. -/
theorem sum_excess_eq (hm : 0 < m) (hn : 0 < n) :
    ∑ A : ValidTable n m, ((totalDepth A.1 hn univ : ℤ) - cdepth m) =
      2 ^ n * ∑ k ∈ range (n + 1), (Nat.stirlingSecond n k : ℤ) * Bint hm k := by
  -- (a) sum over all tables of `excessL`
  have ha : ∑ A : ValidTable n m, ((totalDepth A.1 hn univ : ℤ) - cdepth m) =
      ∑ A : Table n m, excessL m (List.ofFn A) := by
    rw [← Finset.sum_subtype (univ.filter DistinctColumns) (fun A => by simp)
      (fun A => (totalDepth A hn univ : ℤ) - cdepth m), Finset.sum_filter]
    apply sum_congr rfl; intro A _
    unfold excessL
    rw [totalDepth_eq_ldepth]
    by_cases h : DistinctColumns A
    · rw [if_pos h, if_pos ((sep_iff_distinct A).mpr h)]
    · rw [if_neg h, if_neg (fun h' => h ((sep_iff_distinct A).mp h'))]
  -- (b) split each row into its type and its orientation
  have hb : ∑ A : Table n m, excessL m (List.ofFn A) =
      2 ^ n * ∑ τ : Fin n → Ty m hm, excessT hm (List.ofFn τ) := by
    rw [← (rowsEquiv hm).symm.sum_comp, Fintype.sum_prod_type, mul_sum]
    apply sum_congr rfl; intro τ _
    have : ∀ o : Fin n → Bool, excessL m (List.ofFn ((rowsEquiv hm).symm (τ, o))) =
        excessT hm (List.ofFn τ) := by
      intro o
      rw [← excessL_canon hm, List.map_ofFn]
      unfold excessT
      rw [List.map_ofFn]
      congr 2
      funext r
      have := congrArg (fun p => (p.1 r).1) ((rowsEquiv hm).apply_symm_apply (τ, o))
      exact this
    rw [sum_congr rfl (fun o _ => this o), sum_const, card_univ, Fintype.card_fun, Fintype.card_bool,
      Fintype.card_fin, nsmul_eq_mul]
    push_cast; ring
  -- (c) the first appearances
  have hc : ∀ τ : Fin n → Ty m hm, excessT hm (List.ofFn τ) = excessT hm (firsts (List.ofFn τ)) :=
    fun τ => (excessT_firsts hm _).symm
  rw [ha, hb, sum_congr rfl (fun τ _ => hc τ), sum_firsts n (excessT hm)]
  rfl

/-! ## The exponential sum -/

theorem Bint_eq_zero_of_gt (hm : 0 < m) {k : ℕ} (hk : numTypes hm < k) : Bint hm k = 0 := by
  unfold Bint embSum
  have : IsEmpty (Fin k ↪ Ty m hm) := by
    rw [← Fintype.card_eq_zero_iff, Fintype.card_embedding_eq, Fintype.card_fin]
    exact Nat.descFactorial_eq_zero_iff_lt.mpr hk
  simp

theorem sum_range_stirling (hm : 0 < m) (n : ℕ) :
    ∑ k ∈ range (n + 1), (Nat.stirlingSecond n k : ℤ) * Bint hm k =
      ∑ k ∈ range (numTypes hm + 1), (Nat.stirlingSecond n k : ℤ) * Bint hm k := by
  have h1 : ∑ k ∈ range (n + 1), (Nat.stirlingSecond n k : ℤ) * Bint hm k =
      ∑ k ∈ range (n + numTypes hm + 1), (Nat.stirlingSecond n k : ℤ) * Bint hm k := by
    apply sum_subset (range_subset_range.mpr (by omega))
    intro k hk hk'
    simp only [mem_range] at hk hk'
    rw [Nat.stirlingSecond_eq_zero_of_lt (by omega)]; simp
  have h2 : ∑ k ∈ range (numTypes hm + 1), (Nat.stirlingSecond n k : ℤ) * Bint hm k =
      ∑ k ∈ range (n + numTypes hm + 1), (Nat.stirlingSecond n k : ℤ) * Bint hm k := by
    apply sum_subset (range_subset_range.mpr (by omega))
    intro k hk hk'
    simp only [mem_range] at hk hk'
    rw [Bint_eq_zero_of_gt hm (by omega)]; simp
  rw [h1, h2]

theorem stirling_real (n k : ℕ) :
    (Nat.stirlingSecond n k : ℝ) = (stirT n k : ℝ) / k.factorial := by
  have := factorial_mul_stirlingSecond n k
  have hf : (k.factorial : ℝ) ≠ 0 := by exact_mod_cast (Nat.factorial_pos k).ne'
  rw [eq_div_iff hf, ← this]
  push_cast; ring

/-- `2^n ∑_k S(n,k) B_k = N_m(n)` for `n ≥ 1`. -/
theorem numer_eq (hm : 0 < m) (hn : 0 < n) :
    (2 : ℝ) ^ n * (∑ k ∈ range (numTypes hm + 1), (Nat.stirlingSecond n k : ℝ) * Bint hm k) / m =
      numer hm n := by
  set M := numTypes hm
  have hm' : (m : ℝ) ≠ 0 := by exact_mod_cast hm.ne'
  -- expand `S(n,k)` and extend the inner sum to `j ≤ M`
  have hexp : ∀ k ∈ range (M + 1), (2 : ℝ) ^ n * ((Nat.stirlingSecond n k : ℝ) * Bint hm k) / m =
      ∑ j ∈ range (M + 1), (-1 : ℝ) ^ (k - j) * (k.choose j : ℝ) * Bk hm k / k.factorial *
        (2 * j : ℝ) ^ n := by
    intro k hk
    rw [stirling_real, stirT]
    push_cast
    rw [← sum_subset (range_subset_range.mpr (show k + 1 ≤ M + 1 by simp at hk; omega))]
    · rw [sum_div, sum_mul, mul_sum, sum_div]
      apply sum_congr rfl; intro j _
      unfold Bk
      rw [mul_pow]
      field_simp
    · intro j _ hj
      simp only [mem_range, not_lt] at hj
      rw [Nat.choose_eq_zero_of_lt (by omega)]; simp
  rw [mul_sum, sum_div, sum_congr rfl hexp, sum_comm]
  unfold numer coeffA
  rw [sum_range_succ']
  simp only [Nat.cast_zero, mul_zero, zero_pow hn.ne', mul_zero, sum_const_zero, add_zero]
  have hIcc : Icc 1 (numTypes hm) = (range (numTypes hm)).map ⟨(· + 1), add_left_injective 1⟩ := by
    ext j; simp only [mem_Icc, mem_map, mem_range, Function.Embedding.coeFn_mk]
    constructor
    · intro h; exact ⟨j - 1, by omega, by omega⟩
    · rintro ⟨i, hi, rfl⟩; omega
  rw [hIcc, sum_map]
  apply sum_congr rfl; intro j _
  rw [sum_mul]
  apply sum_congr rfl; intro k _
  push_cast
  simp only [Function.Embedding.coeFn_mk, Nat.cast_add, Nat.cast_one]

/-- **Proposition 3.3.** For `2 ≤ m ≤ 2^n`, `t_{n,m}(G) - C(m) = N_m(n) / (2^n)_m`. -/
theorem prop_small_m (hm2 : 2 ≤ m) (hsize : m ≤ 2 ^ n) (hn : 0 < n) :
    tG n m hn - completeCost m = numer (by omega : 0 < m) n / ((2 ^ n).descFactorial m : ℝ) := by
  have hm : 0 < m := by omega
  rw [tG_sub_completeCost hn hm2 hsize, card_valid, ← numer_eq hm hn]
  have hsum : (∑ A : ValidTable n m, ((totalDepth A.1 hn univ : ℝ) - cdepth m)) =
      (2 : ℝ) ^ n * ∑ k ∈ range (numTypes hm + 1), (Nat.stirlingSecond n k : ℝ) * Bint hm k := by
    have := congrArg (fun z : ℤ => (z : ℝ)) (sum_excess_eq hm hn)
    simp only [sum_range_stirling hm n] at this
    push_cast at this
    exact this
  rw [hsum]
  have hm' : (m : ℝ) ≠ 0 := by exact_mod_cast hm.ne'
  rw [div_div, mul_comm (m : ℝ)]

/-! ## Properties of `B_k` -/

/-- The table whose rows are the types `e_0, …, e_{k-1}`. -/
def tblOf (hm : 0 < m) {k : ℕ} (e : Fin k ↪ Ty m hm) : Table k m := fun i => (e i).1

theorem excessT_emb (hm : 0 < m) {k : ℕ} (e : Fin k ↪ Ty m hm) (hk : 0 < k) :
    excessT hm (List.ofFn e) = if DistinctColumns (tblOf hm e) then
      (totalDepth (tblOf hm e) hk univ : ℤ) - cdepth m else 0 := by
  unfold excessT excessL
  rw [List.map_ofFn, totalDepth_eq_ldepth]
  have : (Subtype.val ∘ ⇑e) = tblOf hm e := rfl
  rw [this]
  by_cases h : DistinctColumns (tblOf hm e)
  · rw [if_pos ((sep_iff_distinct _).mpr h), if_pos h]
  · rw [if_neg (fun h' => h ((sep_iff_distinct _).mp h')), if_neg h]

theorem excessT_emb_zero (hm2 : 2 ≤ m) (e : Fin 0 ↪ Ty m (by omega)) :
    excessT (by omega) (List.ofFn e) = 0 := by
  unfold excessT excessL
  rw [if_neg]
  intro h
  obtain ⟨r, hr, -⟩ := h ⟨0, by omega⟩ ⟨1, by omega⟩ (by simp [Fin.ext_iff])
  simp at hr

theorem excessT_nonneg (hm2 : 2 ≤ m) {k : ℕ} (e : Fin k ↪ Ty m (by omega)) :
    0 ≤ excessT (by omega) (List.ofFn e) := by
  rcases Nat.eq_zero_or_pos k with rfl | hk
  · rw [excessT_emb_zero hm2]
  rw [excessT_emb _ e hk]
  split_ifs with h
  · have := cdepth_le_totalDepth (tblOf _ e) h hk univ
    rw [card_univ, Fintype.card_fin] at this
    omega
  · exact le_rfl

/-- `B_k ≥ 0`. -/
theorem Bint_nonneg (hm2 : 2 ≤ m) (k : ℕ) : 0 ≤ Bint (by omega : 0 < m) k :=
  sum_nonneg (fun e _ => excessT_nonneg hm2 e)

/-- If `m ≤ 3`, all `B_k` vanish. -/
theorem Bint_small (hm2 : 2 ≤ m) (hm3 : m ≤ 3) (k : ℕ) : Bint (by omega : 0 < m) k = 0 := by
  apply sum_eq_zero
  intro e _
  rcases Nat.eq_zero_or_pos k with rfl | hk
  · exact excessT_emb_zero hm2 e
  rw [excessT_emb _ e hk]
  split_ifs with h
  · rw [totalDepth_le_three _ h hk univ (by rw [card_univ, Fintype.card_fin]; exact hm3), card_univ,
      Fintype.card_fin]; ring
  · rfl

/-- With all `M` types, every fork splits its candidate set as evenly as possible: `B_M = 0`. -/
theorem Bint_numTypes (hm2 : 2 ≤ m) : Bint (by omega : 0 < m) (numTypes (by omega : 0 < m)) = 0 := by
  have hm : 0 < m := by omega
  apply sum_eq_zero
  intro e _
  have hsurj : Function.Surjective e := by
    have := (Fintype.bijective_iff_injective_and_card e).mpr
      ⟨e.injective, by rw [Fintype.card_fin]; rfl⟩
    exact this.2
  have hk : 0 < numTypes hm := Fintype.card_pos_iff.mpr ⟨⟨fun _ => false, rfl⟩⟩
  rw [excessT_emb hm e hk]
  split_ifs with h
  · rw [totalDepth_eq_cdepth_of_balanced _ h hk ?_ univ, card_univ, Fintype.card_fin]; ring
    intro S
    obtain ⟨X, hXS, hX⟩ := Finset.exists_subset_card_eq (show S.card / 2 ≤ S.card from Nat.div_le_self _ _)
    let ρ : Row m := fun k => decide (k ∈ X)
    obtain ⟨i, hi⟩ := hsurj ⟨canon hm ρ, canon_zero hm ρ⟩
    refine ⟨i, ?_⟩
    have hq : quality (tblOf hm e) S i = rq S (canon hm ρ) := by
      unfold quality ones zeros rq tblOf; rw [hi]
    rw [hq, rq_canon]
    unfold rq
    have e1 : S.filter (fun k => ρ k = true) = X := by
      ext k; simp only [ρ, mem_filter, decide_eq_true_eq]; exact ⟨fun h => h.2, fun h => ⟨hXS h, h⟩⟩
    have e2 : (S.filter (fun k => ρ k = false)).card = S.card - X.card := by
      have := card_filter_add_card_filter_not (s := S) (fun k => ρ k = true)
      rw [e1] at this
      have e3 : S.filter (fun k => ¬ρ k = true) = S.filter (fun k => ρ k = false) := by
        congr 1; ext k; simp
      rw [e3] at this; omega
    rw [e1, e2, hX]
    omega
  · rfl

/-- The comb: the `m - 1` types that single out columns `1, …, m-1`. -/
def combEmb (hm : 0 < m) : Fin (m - 1) ↪ Ty m hm where
  toFun i := ⟨combTable m i, by simp [combTable]⟩
  inj' i i' h := by
    have := congrFun (congrArg Subtype.val h) ⟨i.val + 1, by omega⟩
    simp [combTable] at this
    exact Fin.ext this

/-- `B_{m-1} > 0` for `m ≥ 4`. -/
theorem Bint_comb (hm4 : 4 ≤ m) : 0 < Bint (by omega : 0 < m) (m - 1) := by
  have hm : 0 < m := by omega
  have hk : 0 < m - 1 := by omega
  apply sum_pos' (fun e _ => excessT_nonneg (by omega) e)
  refine ⟨combEmb hm, mem_univ _, ?_⟩
  rw [excessT_emb hm _ hk]
  have ht : tblOf hm (combEmb hm) = combTable m := rfl
  rw [ht, if_pos (combTable_distinct m)]
  have := comb_excess m hm4 hk
  omega

theorem numTypes_eq (hm : 0 < m) : numTypes hm = 2 ^ (m - 1) := by
  unfold numTypes
  rw [Fintype.card_subtype]
  have hadd := card_filter_add_card_filter_not (s := (univ : Finset (Row m))) (fun r => r ⟨0, hm⟩ = false)
  rw [card_univ, Fintype.card_fun, Fintype.card_fin, Fintype.card_bool] at hadd
  have himg : (univ : Finset (Row m)).filter (fun r => ¬r ⟨0, hm⟩ = false) =
      ((univ : Finset (Row m)).filter (fun r => r ⟨0, hm⟩ = false)).image (fun r k => !r k) := by
    ext r
    simp only [mem_filter, mem_univ, true_and, mem_image]
    constructor
    · intro h; exact ⟨fun k => !r k, by simpa using h, by funext k; simp⟩
    · rintro ⟨q, hq, rfl⟩; simp [hq]
  have hinj : Function.Injective (fun (r : Row m) k => !r k) := by
    intro r q h; funext k; simpa using congrFun h k
  rw [himg, card_image_of_injective _ hinj] at hadd
  have hp : 2 ^ m = 2 * 2 ^ (m - 1) := by rw [← pow_succ']; congr 1; omega
  omega

/-! ## The leading index `J` -/

theorem J_nonempty (hm4 : 4 ≤ m) :
    ((range (numTypes (by omega : 0 < m) + 1)).filter (fun k => 0 < Bint (by omega : 0 < m) k)).Nonempty := by
  refine ⟨m - 1, mem_filter.mpr ⟨mem_range.mpr ?_, Bint_comb hm4⟩⟩
  rw [numTypes_eq]
  have := Nat.lt_two_pow_self (n := m - 1)
  omega

/-- `J = max {k : B_k > 0}`. -/
def J (hm4 : 4 ≤ m) : ℕ :=
  ((range (numTypes (by omega : 0 < m) + 1)).filter (fun k => 0 < Bint (by omega : 0 < m) k)).max'
    (J_nonempty hm4)

theorem Bint_J_pos (hm4 : 4 ≤ m) : 0 < Bint (by omega : 0 < m) (J hm4) :=
  (mem_filter.mp (max'_mem _ (J_nonempty hm4))).2

theorem Bint_eq_zero_of_J_lt (hm4 : 4 ≤ m) {k : ℕ} (hk : J hm4 < k) : Bint (by omega : 0 < m) k = 0 := by
  by_cases hkM : k ≤ numTypes (by omega : 0 < m)
  · have hle := Bint_nonneg (by omega : 2 ≤ m) k
    by_contra hne
    have hmem : k ∈ (range (numTypes (by omega : 0 < m) + 1)).filter
        (fun k => 0 < Bint (by omega : 0 < m) k) :=
      mem_filter.mpr ⟨mem_range.mpr (by omega), lt_of_le_of_ne hle (Ne.symm hne)⟩
    have := le_max' _ k hmem
    unfold J at hk
    omega
  · exact Bint_eq_zero_of_gt _ (by omega)

/-- `m - 1 ≤ J < M`. -/
theorem J_bounds (hm4 : 4 ≤ m) : m - 1 ≤ J hm4 ∧ J hm4 < numTypes (by omega : 0 < m) := by
  constructor
  · apply le_max'
    refine mem_filter.mpr ⟨mem_range.mpr ?_, Bint_comb hm4⟩
    rw [numTypes_eq]; have := Nat.lt_two_pow_self (n := m - 1); omega
  · have hmem := mem_filter.mp (max'_mem _ (J_nonempty hm4))
    have hle : J hm4 ≤ numTypes (by omega : 0 < m) := by
      have := mem_range.mp hmem.1; unfold J; omega
    rcases lt_or_eq_of_le hle with h | h
    · exact h
    · have := Bint_J_pos hm4
      rw [h, Bint_numTypes (by omega)] at this
      exact absurd this (lt_irrefl 0)

/-- `a_J = B_J / J! > 0`. -/
theorem coeffA_J (hm4 : 4 ≤ m) :
    coeffA (by omega : 0 < m) (J hm4) = Bk (by omega : 0 < m) (J hm4) / (J hm4).factorial ∧
      0 < coeffA (by omega : 0 < m) (J hm4) := by
  have hm : 0 < m := by omega
  have hJ : coeffA hm (J hm4) = Bk hm (J hm4) / (J hm4).factorial := by
    unfold coeffA
    rw [sum_eq_single (J hm4)]
    · simp
    · intro k _ hk
      rcases lt_or_gt_of_ne hk with h | h
      · rw [Nat.choose_eq_zero_of_lt h]; simp
      · unfold Bk; rw [Bint_eq_zero_of_J_lt hm4 h]; simp
    · intro h
      exact absurd (mem_range.mpr (Nat.lt_succ_of_lt (J_bounds hm4).2)) h
  refine ⟨hJ, ?_⟩
  rw [hJ]
  unfold Bk
  have := Bint_J_pos hm4
  have : (0 : ℝ) < Bint hm (J hm4) := by exact_mod_cast this
  positivity

end GradientKey.Concrete
