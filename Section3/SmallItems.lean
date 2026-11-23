import SmallM

/-!
# Small items of Proposition 3.3

* `prop32_stirling_identity`: `k! S(n,k) = ∑_j (-1)^(k-j) C(k,j) j^n`.
* `prop32_stirling_form`: `N_m(n) = 2^n ∑_{k=0}^{M} B_k S(n,k)` (the first form in Proposition 3.3).
* `Bk_eq_tuple_sum`: `B_k` is the sum of `L̄(G(T)) - C(m)` over the ordered `k`-tuples `T` of distinct
  row types that separate the columns; `T` is an embedding `Fin k ↪ Ty m hm`, and `G(T)` is built from the
  table `tblOf hm T` of its canonical representatives (the rows with a `0` in column `0`).
* `numer_eq_zero_of_two_pow_lt`: `N_m(n) = 0` for `n ≥ 1` and `2^n < m`.
-/

noncomputable section

namespace GradientKey.Concrete
open Classical Finset

variable {n m : ℕ}

/-- `k! S(n,k) = ∑_{j=0}^{k} (-1)^(k-j) C(k,j) j^n`. -/
theorem prop32_stirling_identity (n k : ℕ) :
    ((k.factorial * Nat.stirlingSecond n k : ℕ) : ℤ) =
      ∑ j ∈ range (k + 1), (-1 : ℤ) ^ (k - j) * (k.choose j : ℤ) * (j : ℤ) ^ n :=
  factorial_mul_stirlingSecond n k

/-- Proposition 3.3, first form: `N_m(n) = 2^n ∑_{k=0}^{M} B_k S(n,k)` for `n ≥ 1`. -/
theorem prop32_stirling_form (hm : 0 < m) (hn : 0 < n) :
    numer hm n = (2 : ℝ) ^ n * ∑ k ∈ range (numTypes hm + 1), Bk hm k * (Nat.stirlingSecond n k : ℝ) := by
  rw [← numer_eq hm hn, mul_div_assoc, sum_div]
  congr 1
  apply sum_congr rfl
  intro k _
  unfold Bk
  ring

/-- `B_k` as in the article: the sum of `L̄(G(T)) - C(m)` over the ordered `k`-tuples `T` of distinct
row types that separate the columns. -/
theorem Bk_eq_tuple_sum (hm : 0 < m) (k : ℕ) (hk : 0 < k) :
    Bk hm k =
      ∑ e : Fin k ↪ Ty m hm,
        if DistinctColumns (tblOf hm e) then cost (tblOf hm e) hk - completeCost m else 0 := by
  have hterm (e : Fin k ↪ Ty m hm) :
      ((excessT hm (List.ofFn e) : ℤ) : ℝ) / m =
        (if DistinctColumns (tblOf hm e) then cost (tblOf hm e) hk - completeCost m else 0) := by
    rw [excessT_emb hm e hk]
    by_cases h : DistinctColumns (tblOf hm e)
    · rw [if_pos h, if_pos h]
      unfold cost
      rw [← cdepth_div hm]
      have hs := sum_leafDepth_eq_totalDepth (tblOf hm e) h hk
      have hs' : (∑ j : Fin m, (leafDepth (tblOf hm e) hk j : ℝ)) =
          (totalDepth (tblOf hm e) hk univ : ℝ) := by
        exact_mod_cast hs
      rw [hs']
      push_cast
      ring
    · rw [if_neg h, if_neg h]
      simp
  unfold Bk Bint embSum
  rw [Int.cast_sum, sum_div]
  exact sum_congr rfl (fun e _ => hterm e)

/-- `N_m(n) = 0` for `n ≥ 1` and `2^n < m`: no `n` row types separate the columns. -/
theorem numer_eq_zero_of_two_pow_lt (hm : 0 < m) (hn : 0 < n) (hsmall : 2 ^ n < m) :
    numer hm n = 0 := by
  have hempty : IsEmpty (ValidTable n m) := by
    rw [← Fintype.card_eq_zero_iff, card_valid]
    exact Nat.descFactorial_eq_zero_iff_lt.mpr hsmall
  have h := sum_excess_eq (n := n) hm hn
  rw [Fintype.sum_empty] at h
  have hsum0 : (∑ k ∈ range (n + 1), (Nat.stirlingSecond n k : ℤ) * Bint hm k) = 0 := by
    have hpow : (2 ^ n : ℤ) ≠ 0 := by positivity
    exact (mul_eq_zero.mp h.symm).resolve_left hpow
  have hsum : (∑ k ∈ range (numTypes hm + 1), (Nat.stirlingSecond n k : ℝ) * Bint hm k) = 0 := by
    have hz := congrArg (fun z : ℤ => (z : ℝ)) ((sum_range_stirling hm n).symm.trans hsum0)
    push_cast at hz
    exact hz
  rw [← numer_eq hm hn, hsum]
  ring

end GradientKey.Concrete
