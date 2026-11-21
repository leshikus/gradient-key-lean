import Mathlib

/-!
# `k! S(n,k) = ∑_j (-1)^(k-j) C(k,j) j^n`

The inclusion–exclusion formula for the Stirling numbers of the second kind, from the recurrence
`S(n+1,k+1) = (k+1) S(n,k+1) + S(n,k)` of `Nat.stirlingSecond`. It holds for all `n ≥ 0` (with `0^0 = 1`).
-/

namespace GradientKey.Concrete

open Finset

/-- `T(n,k) = ∑_{j ≤ k} (-1)^(k-j) C(k,j) j^n`. -/
def stirT (n k : ℕ) : ℤ := ∑ j ∈ range (k + 1), (-1) ^ (k - j) * (k.choose j : ℤ) * (j : ℤ) ^ n

theorem stirT_zero (k : ℕ) : stirT 0 k = 0 ^ k := by
  unfold stirT
  have := add_pow (1 : ℤ) (-1) k
  rw [show (1 : ℤ) + -1 = 0 by ring] at this
  rw [this]
  apply sum_congr rfl
  intro j _
  simp only [pow_zero, one_pow, mul_one, one_mul]

theorem stirT_succ_zero (n : ℕ) : stirT (n + 1) 0 = 0 := by simp [stirT]

theorem stirT_succ_succ (n k : ℕ) :
    stirT (n + 1) (k + 1) = (k + 1) * (stirT n (k + 1) + stirT n k) := by
  set U : ℤ := ∑ i ∈ range (k + 1), (-1) ^ (k - i) * (k.choose i : ℤ) * ((i : ℤ) + 1) ^ n
  have hA : stirT (n + 1) (k + 1) = (k + 1) * U := by
    unfold stirT
    rw [sum_range_succ']
    simp only [Nat.cast_zero, zero_pow (Nat.succ_ne_zero n), mul_zero, add_zero]
    rw [mul_sum]
    apply sum_congr rfl
    intro i _
    have hc : ((k + 1).choose (i + 1) : ℤ) * ((i : ℤ) + 1) = ((k : ℤ) + 1) * (k.choose i : ℤ) := by
      have := Nat.add_one_mul_choose_eq k i
      exact_mod_cast this.symm
    rw [show k + 1 - (i + 1) = k - i by omega]
    push_cast
    rw [pow_succ]
    linear_combination ((-1 : ℤ) ^ (k - i) * ((i : ℤ) + 1) ^ n) * hc
  have hB : stirT n (k + 1) + stirT n k = U := by
    unfold stirT
    rw [sum_range_succ' _ (k + 1)]
    have hsplit : ∀ i ∈ range (k + 1), (-1 : ℤ) ^ (k + 1 - (i + 1)) * (((k + 1).choose (i + 1) : ℕ) : ℤ) *
        (((i + 1 : ℕ) : ℤ)) ^ n = (-1) ^ (k - i) * (k.choose i : ℤ) * ((i : ℤ) + 1) ^ n +
          (-1) ^ (k - i) * (k.choose (i + 1) : ℤ) * ((i : ℤ) + 1) ^ n := by
      intro i _
      rw [show k + 1 - (i + 1) = k - i by omega, Nat.choose_succ_succ']
      push_cast; ring
    rw [sum_congr rfl hsplit, sum_add_distrib]
    -- the second sum is `-(T(n,k) - (-1)^k 0^n)`
    have hV : ∑ i ∈ range (k + 1), (-1 : ℤ) ^ (k - i) * (k.choose (i + 1) : ℤ) * ((i : ℤ) + 1) ^ n =
        -(∑ j ∈ range (k + 1), (-1) ^ (k - j) * (k.choose j : ℤ) * (j : ℤ) ^ n) +
          (-1) ^ k * (0 : ℤ) ^ n := by
      rw [sum_range_succ, Nat.choose_succ_self, Nat.cast_zero, mul_zero, zero_mul, add_zero]
      rw [sum_range_succ' _ k]
      simp only [Nat.cast_zero, Nat.sub_zero, Nat.choose_zero_right, Nat.cast_one, mul_one]
      rw [neg_add, ← sum_neg_distrib, neg_add_cancel_right]
      apply sum_congr rfl
      intro i hi
      have hik : i < k := mem_range.mp hi
      rw [show k - i = (k - (i + 1)) + 1 by omega, pow_succ]
      push_cast; ring
    rw [hV]
    simp only [Nat.cast_zero, Nat.sub_zero, Nat.choose_zero_right, Nat.cast_one, mul_one]
    rw [pow_succ]
    ring
  rw [hA, hB]

/-- **Stirling numbers**: `k! S(n,k) = ∑_{j ≤ k} (-1)^(k-j) C(k,j) j^n`. -/
theorem factorial_mul_stirlingSecond (n k : ℕ) :
    ((k.factorial * Nat.stirlingSecond n k : ℕ) : ℤ) = stirT n k := by
  induction n generalizing k with
  | zero =>
    rw [stirT_zero]
    cases k with
    | zero => simp
    | succ k => simp
  | succ n ih =>
    cases k with
    | zero => simp [stirT_succ_zero]
    | succ k =>
      rw [stirT_succ_succ, ← ih, ← ih, Nat.stirlingSecond_succ_succ, Nat.factorial_succ]
      push_cast
      ring

end GradientKey.Concrete
