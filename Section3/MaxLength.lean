import SmallM
import BkInteger

/-!
# Maximum length (remark after Table 1)

The counting argument of Proposition 3.3 uses only that the statistic of a table depends on the
list of its row types in order of first appearance and vanishes when the rows do not separate
the columns. For any such integer statistic `Φ` of row lists,
`∑_{A ∈ 𝒜_{n,m}} Φ(A) = 2^n ∑_k S(n,k) B_k(Φ)`, with `B_k(Φ)` the sum of `Φ` over the ordered
`k`-tuples of distinct types (`sum_stat_eq`), and `= ∑_{j=1}^M a_j(Φ) (2j)^n` for `n ≥ 1`
(`sum_stat_numer`). For `Φ = D - cdepth m` this is `sum_excess_eq` (`statB_excess`).

For the maximum length `L_max = max_j L_j` and `Φ = L_max - ⌈log m⌉`:
`t^max_{n,m}(G) - ⌈log m⌉ = N^max_m(n) / (2^n)_m` (`prop_max_length`), and
`N^max_m(n) = 2^n ∑_k B^max_k S(n,k)` (`prop_max_length_stirling`).
-/

noncomputable section

namespace GradientKey.Concrete

open Finset

variable {n m : ℕ}

open Classical in
/-- `B_k(Φ)`: the sum of `Φ` over the ordered `k`-tuples of distinct types. -/
def statB (hm : 0 < m) (Φ : List (Row m) → ℤ) (k : ℕ) : ℤ :=
  embSum (fun t : List (Ty m hm) => Φ (t.map Subtype.val)) k

open Classical in
/-- `∑_{A ∈ 𝒜_{n,m}} Φ(A) = 2^n ∑_k S(n,k) B_k(Φ)`. -/
theorem sum_stat_eq (hm : 0 < m) (Φ : List (Row m) → ℤ)
    (hcanon : ∀ L, Φ (L.map (canon hm)) = Φ L)
    (hfirsts : ∀ L, Φ (firsts L) = Φ L)
    (hzero : ∀ L, ¬ Sep L → Φ L = 0) :
    ∑ A : ValidTable n m, Φ (List.ofFn A.1) =
      2 ^ n * ∑ k ∈ range (n + 1), (Nat.stirlingSecond n k : ℤ) * statB hm Φ k := by
  have ha : ∑ A : ValidTable n m, Φ (List.ofFn A.1) = ∑ A : Table n m, Φ (List.ofFn A) := by
    rw [← Finset.sum_subtype (univ.filter DistinctColumns) (fun A => by simp)
      (fun A => Φ (List.ofFn A)), Finset.sum_filter]
    apply sum_congr rfl; intro A _
    by_cases h : DistinctColumns A
    · rw [if_pos h]
    · rw [if_neg h, hzero _ (fun h' => h ((sep_iff_distinct A).mp h'))]
  have hb : ∑ A : Table n m, Φ (List.ofFn A) =
      2 ^ n * ∑ τ : Fin n → Ty m hm, Φ ((List.ofFn τ).map Subtype.val) := by
    rw [← (rowsEquiv hm).symm.sum_comp, Fintype.sum_prod_type, mul_sum]
    apply sum_congr rfl; intro τ _
    have : ∀ o : Fin n → Bool, Φ (List.ofFn ((rowsEquiv hm).symm (τ, o))) =
        Φ ((List.ofFn τ).map Subtype.val) := by
      intro o
      rw [← hcanon, List.map_ofFn, List.map_ofFn]
      congr 2
      funext r
      exact congrArg (fun p => (p.1 r).1) ((rowsEquiv hm).apply_symm_apply (τ, o))
    rw [sum_congr rfl (fun o _ => this o), sum_const, card_univ, Fintype.card_fun,
      Fintype.card_bool, Fintype.card_fin, nsmul_eq_mul]
    push_cast; ring
  have hc : ∀ τ : Fin n → Ty m hm, Φ ((List.ofFn τ).map Subtype.val) =
      Φ ((firsts (List.ofFn τ)).map Subtype.val) := by
    intro τ
    rw [map_firsts _ Subtype.val_injective, hfirsts]
  rw [ha, hb, sum_congr rfl (fun τ _ => hc τ),
    sum_firsts n (fun t : List (Ty m hm) => Φ (t.map Subtype.val))]
  rfl

/-- The excess `D - cdepth m` is an instance: `B_k(D - cdepth m) = m B_k`. -/
theorem statB_excess (hm : 0 < m) : statB hm (excessL m) = Bint hm := rfl

theorem statB_eq_zero_of_gt (hm : 0 < m) (Φ : List (Row m) → ℤ) {k : ℕ}
    (hk : numTypes hm < k) : statB hm Φ k = 0 := by
  unfold statB embSum
  have : IsEmpty (Fin k ↪ Ty m hm) := by
    rw [← Fintype.card_eq_zero_iff, Fintype.card_embedding_eq, Fintype.card_fin]
    exact Nat.descFactorial_eq_zero_iff_lt.mpr hk
  simp

theorem sum_stat_range (hm : 0 < m) (Φ : List (Row m) → ℤ) (n : ℕ) :
    ∑ k ∈ range (n + 1), (Nat.stirlingSecond n k : ℤ) * statB hm Φ k =
      ∑ k ∈ range (numTypes hm + 1), (Nat.stirlingSecond n k : ℤ) * statB hm Φ k := by
  have h1 : ∑ k ∈ range (n + 1), (Nat.stirlingSecond n k : ℤ) * statB hm Φ k =
      ∑ k ∈ range (n + numTypes hm + 1), (Nat.stirlingSecond n k : ℤ) * statB hm Φ k := by
    apply sum_subset (range_subset_range.mpr (by omega))
    intro k hk hk'
    simp only [mem_range] at hk hk'
    rw [Nat.stirlingSecond_eq_zero_of_lt (by omega)]; simp
  have h2 : ∑ k ∈ range (numTypes hm + 1), (Nat.stirlingSecond n k : ℤ) * statB hm Φ k =
      ∑ k ∈ range (n + numTypes hm + 1), (Nat.stirlingSecond n k : ℤ) * statB hm Φ k := by
    apply sum_subset (range_subset_range.mpr (by omega))
    intro k hk hk'
    simp only [mem_range] at hk hk'
    rw [statB_eq_zero_of_gt hm Φ (by omega)]; simp
  rw [h1, h2]

/-- `a_j(Φ) = ∑_{k ≥ j} (-1)^(k-j) C(k,j) B_k(Φ) / k!`. -/
def statA (hm : 0 < m) (Φ : List (Row m) → ℤ) (j : ℕ) : ℝ :=
  ∑ k ∈ range (numTypes hm + 1), (-1 : ℝ) ^ (k - j) * (k.choose j : ℝ) * (statB hm Φ k : ℝ) /
    k.factorial

/-- `N_m(n; Φ) = ∑_{j=1}^M a_j(Φ) (2j)^n`. -/
def statNumer (hm : 0 < m) (Φ : List (Row m) → ℤ) (n : ℕ) : ℝ :=
  ∑ j ∈ Icc 1 (numTypes hm), statA hm Φ j * (2 * j : ℝ) ^ n

/-- `2^n ∑_k S(n,k) B_k(Φ) = N_m(n; Φ)` for `n ≥ 1`. -/
theorem statNumer_eq (hm : 0 < m) (Φ : List (Row m) → ℤ) (hn : 0 < n) :
    (2 : ℝ) ^ n * (∑ k ∈ range (numTypes hm + 1), (Nat.stirlingSecond n k : ℝ) * (statB hm Φ k : ℝ)) =
      statNumer hm Φ n := by
  set M := numTypes hm
  have hexp : ∀ k ∈ range (M + 1),
      (2 : ℝ) ^ n * ((Nat.stirlingSecond n k : ℝ) * (statB hm Φ k : ℝ)) =
      ∑ j ∈ range (M + 1), (-1 : ℝ) ^ (k - j) * (k.choose j : ℝ) * (statB hm Φ k : ℝ) /
        k.factorial * (2 * j : ℝ) ^ n := by
    intro k hk
    rw [stirling_real, stirT]
    push_cast
    rw [← sum_subset (range_subset_range.mpr (show k + 1 ≤ M + 1 by simp at hk; omega))]
    · rw [sum_div, sum_mul, mul_sum]
      apply sum_congr rfl; intro j _
      rw [mul_pow]
      ring
    · intro j _ hj
      simp only [mem_range, not_lt] at hj
      rw [Nat.choose_eq_zero_of_lt (by omega)]; simp
  rw [mul_sum, sum_congr rfl hexp, sum_comm]
  unfold statNumer statA
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

/-- `∑_{A ∈ 𝒜_{n,m}} Φ(A) = N_m(n; Φ)` for `n ≥ 1`. -/
theorem sum_stat_numer (hm : 0 < m) (Φ : List (Row m) → ℤ) (hn : 0 < n)
    (hcanon : ∀ L, Φ (L.map (canon hm)) = Φ L)
    (hfirsts : ∀ L, Φ (firsts L) = Φ L)
    (hzero : ∀ L, ¬ Sep L → Φ L = 0) :
    (∑ A : ValidTable n m, (Φ (List.ofFn A.1) : ℝ)) = statNumer hm Φ n := by
  have h := congrArg (fun z : ℤ => (z : ℝ)) (sum_stat_eq (n := n) hm Φ hcanon hfirsts hzero)
  simp only [sum_stat_range hm Φ n] at h
  push_cast at h
  rw [← statNumer_eq hm Φ hn]
  exact h

/-! ## The maximum length -/

/-- `L_max` of the greedy tree of a row list. -/
def lmax (L : List (Row m)) : ℕ := (univ : Finset (Fin m)).sup (cdep L)

theorem lmax_canon (hm : 0 < m) (L : List (Row m)) : lmax (L.map (canon hm)) = lmax L := by
  unfold lmax
  rw [show cdep (L.map (canon hm)) = cdep L from funext (cdep_map_canon hm L)]

open Classical in
theorem cdep_firsts (L : List (Row m)) (j : Fin m) : cdep (firsts L) j = cdep L j := by
  have hs : ∀ T j, lstep (firsts L) T j = lstep L T j := by
    intro T j
    unfold lstep
    rw [argmax_firsts]
  unfold cdep
  simp only [lcand_of_lstep hs j]

open Classical in
theorem lmax_firsts (L : List (Row m)) : lmax (firsts L) = lmax L := by
  unfold lmax
  rw [show cdep (firsts L) = cdep L from funext (cdep_firsts L)]

/-- On a table, `cdep` is `L_j`. -/
theorem cdep_ofFn (A : Table n m) (hA : DistinctColumns A) (hn : 0 < n) (j : Fin m) :
    cdep (List.ofFn A) j = leafDepth A hn j := by
  rw [leafDepth_eq_forksN A hA hn]
  unfold cdep forksN
  have hc : ∀ i, candFrom A hn univ j i = lcand (List.ofFn A) j i := by
    intro i
    unfold candFrom lcand
    congr 1
    funext T
    exact candidateStep_eq_lstep A T j hn
  simp only [hc]

theorem lmax_ofFn (A : Table n m) (hA : DistinctColumns A) (hn : 0 < n) :
    lmax (List.ofFn A) = (univ : Finset (Fin m)).sup (leafDepth A hn) := by
  unfold lmax
  rw [show cdep (List.ofFn A) = leafDepth A hn from funext (cdep_ofFn A hA hn)]

/-- `t^max_{n,m}(G)`: the average of `L_max = max_j L_j` over `𝒜_{n,m}`. -/
def tGmax (n m : ℕ) (hn : 0 < n) : ℝ :=
  (∑ A : ValidTable n m, ((univ : Finset (Fin m)).sup (leafDepth A.1 hn) : ℝ)) /
    (Fintype.card (ValidTable n m) : ℝ)

open Classical in
/-- `L_max - ⌈log m⌉` if the rows separate the columns, else `0`. -/
def maxExcess (m : ℕ) (L : List (Row m)) : ℤ :=
  if Sep L then (lmax L : ℤ) - Nat.clog 2 m else 0

/-- `B^max_k`: the sum of `L_max - ⌈log m⌉` over the ordered `k`-tuples of distinct types. -/
def BmaxInt (hm : 0 < m) (k : ℕ) : ℤ := statB hm (maxExcess m) k

/-- `a^max_j`. -/
def coeffAmax (hm : 0 < m) (j : ℕ) : ℝ := statA hm (maxExcess m) j

/-- `N^max_m(n) = ∑_{j=1}^M a^max_j (2j)^n`. -/
def numerMax (hm : 0 < m) (n : ℕ) : ℝ := statNumer hm (maxExcess m) n

theorem maxExcess_canon (hm : 0 < m) (L : List (Row m)) :
    maxExcess m (L.map (canon hm)) = maxExcess m L := by
  unfold maxExcess
  rw [lmax_canon hm]
  by_cases h : Sep L
  · rw [if_pos ((sep_map_canon hm L).mpr h), if_pos h]
  · rw [if_neg (fun h' => h ((sep_map_canon hm L).mp h')), if_neg h]

open Classical in
theorem maxExcess_firsts (L : List (Row m)) : maxExcess m (firsts L) = maxExcess m L := by
  unfold maxExcess
  rw [lmax_firsts]
  by_cases h : Sep L
  · rw [if_pos ((sep_firsts L).mpr h), if_pos h]
  · rw [if_neg (fun h' => h ((sep_firsts L).mp h')), if_neg h]

/-- **Maximum length.** For `2 ≤ m ≤ 2^n`, `t^max_{n,m}(G) - ⌈log m⌉ = N^max_m(n) / (2^n)_m`. -/
theorem prop_max_length (hm2 : 2 ≤ m) (hsize : m ≤ 2 ^ n) (hn : 0 < n) :
    tGmax n m hn - Nat.clog 2 m = numerMax (by omega : 0 < m) n / ((2 ^ n).descFactorial m : ℝ) := by
  have hm : 0 < m := by omega
  have hd : (2 ^ n).descFactorial m ≠ 0 := fun h =>
    absurd (Nat.descFactorial_eq_zero_iff_lt.mp h) (not_lt.mpr hsize)
  have hd' : ((2 ^ n).descFactorial m : ℝ) ≠ 0 := by exact_mod_cast hd
  have hsum := sum_stat_numer (n := n) hm (maxExcess m) hn (maxExcess_canon hm) maxExcess_firsts
    (fun L h => by simp [maxExcess, h])
  have hterm (A : ValidTable n m) : ((maxExcess m (List.ofFn A.1) : ℤ) : ℝ) =
      ((univ : Finset (Fin m)).sup (leafDepth A.1 hn) : ℝ) - Nat.clog 2 m := by
    rw [maxExcess, if_pos ((sep_iff_distinct A.1).mpr A.2), lmax_ofFn A.1 A.2 hn]
    push_cast
    ring
  simp only [hterm, sum_sub_distrib, sum_const, card_univ, nsmul_eq_mul] at hsum
  unfold tGmax numerMax
  rw [← hsum, card_valid]
  field_simp
  all_goals ring

/-- **Maximum length**, Stirling form: `N^max_m(n) = 2^n ∑_k B^max_k S(n,k)` for `n ≥ 1`. -/
theorem prop_max_length_stirling (hm : 0 < m) (hn : 0 < n) :
    numerMax hm n = (2 : ℝ) ^ n * ∑ k ∈ range (numTypes hm + 1),
      (BmaxInt hm k : ℝ) * (Nat.stirlingSecond n k : ℝ) := by
  unfold numerMax BmaxInt
  rw [← statNumer_eq hm (maxExcess m) hn]
  congr 1
  apply sum_congr rfl; intro k _; ring

end GradientKey.Concrete
