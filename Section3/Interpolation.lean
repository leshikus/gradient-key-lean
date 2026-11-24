import NumerZero
import PathFormula
import Mathlib.LinearAlgebra.Vandermonde

/-!
# The computation paragraph of Proposition 3.3: integrality and the Vandermonde system

* `(2^n)_m t_{n,m}(G) = ∑_{A ∈ 𝒜_{n,m}} L_j(A)` for every column `j` (column symmetry from the
  per-chain counts), so `(2^n)_m t_{n,m}(G)` is a natural number (`tG_scaled_natural`).
* For `⌈log m⌉ ≤ n`, `N_m(n) = (2^n)_m t_{n,m}(G) - (2^n)_m C(m)` (`numer_eq_scaled_sub`).
* The `M` values `N_m(0), …, N_m(M-1)` determine `a_1, …, a_M`: the Vandermonde matrix on the
  distinct nodes `2, 4, …, 2M` is invertible (`coeffA_determined`). The sample values are
  `0` for `n = 0` and for `2^n < m`, and `(2^n)_m (t_{n,m}(G) - C(m))` otherwise
  (`sampleNumer_eq`, `coeffA_determined_samples`).
-/

noncomputable section

namespace GradientKey.Concrete

open Finset

variable {n m : ℕ}

open Classical in
/-- Column symmetry: `∑_A L_j(A)` does not depend on the column `j`. -/
theorem sum_table_leafDepth_eq (hn : 0 < n) (j k : Fin m) :
    (∑ A : ValidTable n m, leafDepth A.1 hn j) = ∑ A : ValidTable n m, leafDepth A.1 hn k := by
  rw [sum_leafDepth_eq_sum_forkTableCount hn j, sum_leafDepth_eq_sum_forkTableCount hn k,
    sum_forkTableCount_eq hn j, sum_forkTableCount_eq hn k]
  refine sum_congr rfl fun s _ => ?_
  exact_mod_cast (chain_count hn s j).trans (chain_count hn s k).symm

open Classical in
/-- `∑_A ∑_k L_k(A) = m ∑_A L_j(A)`. -/
theorem sum_table_totalDepth_eq (hn : 0 < n) (j : Fin m) :
    (∑ A : ValidTable n m, totalDepth A.1 hn univ) =
      m * ∑ A : ValidTable n m, leafDepth A.1 hn j := by
  calc
    _ = ∑ A : ValidTable n m, ∑ k : Fin m, leafDepth A.1 hn k :=
      sum_congr rfl fun A _ => (sum_leafDepth_eq_totalDepth A.1 A.2 hn).symm
    _ = ∑ k : Fin m, ∑ A : ValidTable n m, leafDepth A.1 hn k := sum_comm
    _ = ∑ _k : Fin m, ∑ A : ValidTable n m, leafDepth A.1 hn j :=
      sum_congr rfl fun k _ => sum_table_leafDepth_eq hn k j
    _ = _ := by rw [sum_const, card_univ, Fintype.card_fin, smul_eq_mul]

open Classical in
/-- `(2^n)_m t_{n,m}(G) = ∑_{A ∈ 𝒜_{n,m}} L_j(A)` for every column `j`. -/
theorem scaled_tG_eq_column_sum (hn : 0 < n) (hm : 2 ≤ m) (hs : m ≤ 2 ^ n) (j : Fin m) :
    ((2 ^ n).descFactorial m : ℝ) * tG n m hn =
      ((∑ A : ValidTable n m, leafDepth A.1 hn j : ℕ) : ℝ) := by
  have hd : (2 ^ n).descFactorial m ≠ 0 := by
    intro h
    exact absurd (Nat.descFactorial_eq_zero_iff_lt.mp h) (not_lt.mpr hs)
  have hd' : ((2 ^ n).descFactorial m : ℝ) ≠ 0 := by exact_mod_cast hd
  have hm' : (m : ℝ) ≠ 0 := by
    have : (0 : ℝ) < m := by exact_mod_cast (show 0 < m by omega)
    exact this.ne'
  have h1 : (∑ A : ValidTable n m, cost A.1 hn) =
      ((∑ A : ValidTable n m, totalDepth A.1 hn univ : ℕ) : ℝ) / m := by
    unfold cost
    rw [← sum_div, Nat.cast_sum]
    congr 1
    refine sum_congr rfl fun A _ => ?_
    exact_mod_cast sum_leafDepth_eq_totalDepth A.1 A.2 hn
  unfold tG
  rw [h1, card_valid, sum_table_totalDepth_eq hn j]
  push_cast
  field_simp
  all_goals ring

open Classical in
/-- `(2^n)_m t_{n,m}(G)` is a natural number. -/
theorem tG_scaled_natural (hn : 0 < n) (hm : 2 ≤ m) (hs : m ≤ 2 ^ n) :
    ∃ N : ℕ, (N : ℝ) = ((2 ^ n).descFactorial m : ℝ) * tG n m hn :=
  ⟨_, (scaled_tG_eq_column_sum hn hm hs ⟨0, by omega⟩).symm⟩

/-- `N_m(n) = (2^n)_m t_{n,m}(G) - (2^n)_m C(m)` for `2 ≤ m ≤ 2^n`. -/
theorem numer_eq_scaled_sub (hm : 2 ≤ m) (hsize : m ≤ 2 ^ n) (hn : 0 < n) :
    numer (by omega : 0 < m) n =
      ((2 ^ n).descFactorial m : ℝ) * tG n m hn - ((2 ^ n).descFactorial m : ℝ) * completeCost m := by
  have hd : (2 ^ n).descFactorial m ≠ 0 := by
    intro h
    exact absurd (Nat.descFactorial_eq_zero_iff_lt.mp h) (not_lt.mpr hsize)
  have hd' : ((2 ^ n).descFactorial m : ℝ) ≠ 0 := by exact_mod_cast hd
  have h := (eq_div_iff hd').mp (prop_small_m hm hsize hn)
  linear_combination (-1 : ℝ) * h

/-- Distinct nodes: if `∑_j a_j x_j^i = ∑_j b_j x_j^i` for `i < M` with `x_j = 2(j+1)`,
then `a = b`. -/
theorem exponential_coeff_unique (M : ℕ) (a b : Fin M → ℝ)
    (h : ∀ i : Fin M, (∑ j : Fin M, a j * (2 * ((j : ℕ) + 1) : ℝ) ^ (i : ℕ)) =
      ∑ j : Fin M, b j * (2 * ((j : ℕ) + 1) : ℝ) ^ (i : ℕ)) : a = b := by
  have hx : Function.Injective (fun j : Fin M => (2 * ((j : ℕ) + 1) : ℝ)) := by
    intro i j hij
    have hij' : (2 * ((i : ℕ) + 1) : ℝ) = 2 * ((j : ℕ) + 1) := hij
    have h' : ((i : ℕ) : ℝ) = ((j : ℕ) : ℝ) := by linarith
    exact Fin.ext (by exact_mod_cast h')
  have hz : (fun j => a j - b j) = 0 :=
    Matrix.eq_zero_of_forall_pow_sum_mul_pow_eq_zero hx fun i => by
      simp only [sub_mul, sum_sub_distrib]
      rw [h i, sub_self]
  funext j
  exact sub_eq_zero.mp (congrFun hz j)

/-- `∑_{j=1}^M f(j) = ∑_{j : Fin M} f(j+1)`. -/
theorem sum_positive_indices (M : ℕ) (f : ℕ → ℝ) :
    (∑ j ∈ Icc 1 M, f j) = ∑ j : Fin M, f ((j : ℕ) + 1) := by
  have hIcc : Icc 1 M = (range M).map ⟨(· + 1), add_left_injective 1⟩ := by
    ext j
    simp only [mem_Icc, mem_map, mem_range, Function.Embedding.coeFn_mk]
    constructor
    · intro h
      exact ⟨j - 1, by omega, by omega⟩
    · rintro ⟨i, hi, rfl⟩
      omega
  rw [hIcc, sum_map]
  exact (Fin.sum_univ_eq_sum_range (fun i => f (i + 1)) M).symm

/-- `N_m(n) = ∑_{j : Fin M} a_{j+1} (2(j+1))^n`. -/
theorem numer_eq_fin (hm : 0 < m) (n : ℕ) :
    numer hm n = ∑ j : Fin (numTypes hm), coeffA hm ((j : ℕ) + 1) * (2 * ((j : ℕ) + 1) : ℝ) ^ n := by
  unfold numer
  rw [sum_positive_indices]
  refine sum_congr rfl fun j _ => ?_
  push_cast
  all_goals ring

/-- The `M` values `N_m(0), …, N_m(M-1)` determine `a_1, …, a_M`. -/
theorem coeffA_determined (hm : 0 < m) (a : Fin (numTypes hm) → ℝ)
    (h : ∀ i : Fin (numTypes hm),
      (∑ j : Fin (numTypes hm), a j * (2 * ((j : ℕ) + 1) : ℝ) ^ (i : ℕ)) = numer hm i) :
    a = fun j => coeffA hm ((j : ℕ) + 1) := by
  apply exponential_coeff_unique
  intro i
  rw [h i, numer_eq_fin]

open Classical in
/-- The sample values of the computation paragraph: `0` for `n = 0` or `2^n < m`, and
`(2^n)_m (t_{n,m}(G) - C(m))` for `1 ≤ n`, `m ≤ 2^n`. -/
def sampleNumer (m n : ℕ) : ℝ :=
  if hn : 0 < n then
    if m ≤ 2 ^ n then ((2 ^ n).descFactorial m : ℝ) * (tG n m hn - completeCost m) else 0
  else 0

/-- The sample values are `N_m(n)`. -/
theorem sampleNumer_eq (hm : 2 ≤ m) (n : ℕ) : sampleNumer m n = numer (by omega : 0 < m) n := by
  unfold sampleNumer
  split_ifs with hn hs
  · rw [numer_eq_scaled_sub hm hs hn]
    ring
  · exact (numer_eq_zero_of_two_pow_lt (by omega) hn (not_le.mp hs)).symm
  · obtain rfl : n = 0 := by omega
    exact (numer_zero hm).symm

/-- **Computation paragraph.** The coefficients `a_1, …, a_M` are the unique solution of the
Vandermonde system with right-hand sides `N_m(0), …, N_m(M-1)` given by the samples. -/
theorem coeffA_determined_samples (hm : 2 ≤ m) (a : Fin (numTypes (by omega : 0 < m)) → ℝ)
    (h : ∀ i : Fin (numTypes (by omega : 0 < m)),
      (∑ j : Fin (numTypes (by omega : 0 < m)), a j * (2 * ((j : ℕ) + 1) : ℝ) ^ (i : ℕ)) =
        sampleNumer m i) :
    a = fun j => coeffA (by omega : 0 < m) ((j : ℕ) + 1) := by
  apply coeffA_determined
  intro i
  rw [h i, sampleNumer_eq hm]

end GradientKey.Concrete
