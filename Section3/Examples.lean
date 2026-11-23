import SmallItems
import Dense
import NearDense
import NearDense2
import Asymptotic

/-!
# Examples

Exact instances of Propositions 3.3, 3.5 and 3.6:
`(n,m) = (1,2)`, `m = 2`, `m = 2^n`, `(3,4)`, `(4,11)` and `(4,10)`.
-/

noncomputable section

namespace GradientKey.Concrete

/-- `C(2^k) = k`. -/
theorem completeCost_two_pow (k : ℕ) : completeCost (2 ^ k) = k := by
  unfold completeCost
  rw [Nat.log_pow (by norm_num)]
  push_cast
  have h : (2 : ℝ) ^ k ≠ 0 := by positivity
  field_simp
  ring

/-- Proposition 3.5 with `m = 2^n`: `t_{n,2^n}(G) = n`. -/
theorem example_full (n : ℕ) (hn : 0 < n) : tG n (2 ^ n) hn = n := by
  rw [prop_dense hn (by omega) le_rfl (Nat.le_self_pow hn.ne' 2 |>.trans' (by norm_num)),
    completeCost_two_pow]

/-- `(n,m) = (1,2)`: `t_{1,2}(G) = 1`. -/
theorem example_n1_m2 : tG 1 2 (by norm_num) = 1 := by
  have := example_full 1 (by norm_num)
  simpa using this

/-- `m = 2`: `t_{n,2}(G) = 1` for every `n ≥ 1`. -/
theorem example_m2 (n : ℕ) (hn : 0 < n) : tG n 2 hn = 1 := by
  have h := excess_small (n := n) (m := 2) le_rfl (by norm_num)
    (Nat.le_self_pow hn.ne' 2 |>.trans' (by norm_num)) hn
  have hc : completeCost 2 = 1 := by
    simpa using completeCost_two_pow 1
  rw [hc] at h
  linarith

/-- `(n,m) = (3,4)`: `t_{3,4}(G) = 3408/1680 = 2 + 1/35` (Proposition 3.6 with `n = 3`). -/
theorem example_n3_m4 : tG 3 4 (by norm_num) = (3408 : ℝ) / 1680 := by
  have h := prop_near_dense_one (n := 3) (m := 4) le_rfl (by norm_num)
  have hc : completeCost 4 = 2 := by
    simpa using completeCost_two_pow 2
  rw [hc, show Nat.choose (2 ^ 3) (3 + 1) = 70 from rfl] at h
  norm_num at h
  linarith

/-- Proposition 3.6, first formula, `n = 4`: `t_{4,11}(G) - C(11) = 1/3003`. -/
theorem example_n4_m11 :
    tG 4 11 (by norm_num) - completeCost 11 = (1 : ℝ) / 3003 := by
  rw [prop_near_dense_one (n := 4) (m := 11) (by norm_num) (by norm_num),
    show Nat.choose (2 ^ 4) (4 + 1) = 4368 from rfl]
  norm_num

/-- Proposition 3.6, second formula, `n = 4`: `t_{4,10}(G) - C(10) = 18/5005`. -/
theorem example_n4_m10 :
    tG 4 10 (by norm_num) - completeCost 10 = (18 : ℝ) / 5005 := by
  rw [prop_near_dense_two (n := 4) (m := 10) le_rfl (by norm_num),
    show Nat.choose (2 ^ 4) (4 + 2) = 8008 from rfl]
  norm_num

end GradientKey.Concrete
