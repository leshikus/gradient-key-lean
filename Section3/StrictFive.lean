import SmallItems
import Dense

/-!
# The convergence is not monotone: `t_{3,5}(G) = C(5) < t_{4,5}(G)`

The sentence after Corollary 3.4. Proposition 3.5 gives `t_{3,5}(G) = C(5)`. For `n = 4`,
Proposition 3.3 in Stirling form gives `N_5(4) = 2^4 ∑_k B_k S(4,k)`; all `B_k ≥ 0` and
`B_4 > 0` (`B_{m-1} > 0` for `m ≥ 4`), with `S(4,4) = 1`, so `N_5(4) > 0`.
-/

noncomputable section

namespace GradientKey.Concrete

open Finset

open Classical in
/-- `t_{3,5}(G) = C(5) < t_{4,5}(G)`. -/
theorem strict_five :
    tG 3 5 (by norm_num) = completeCost 5 ∧ completeCost 5 < tG 4 5 (by norm_num) := by
  refine ⟨prop_dense (n := 3) (m := 5) (by norm_num) (by norm_num) (by norm_num) (by norm_num), ?_⟩
  have hm : 0 < (5 : ℕ) := by norm_num
  have hb (k : ℕ) : 0 ≤ Bk hm k := by
    unfold Bk
    apply div_nonneg
    · exact_mod_cast Bint_nonneg (m := 5) (by norm_num) k
    · norm_num
  have hp : 0 < Bk hm 4 := by
    unfold Bk
    apply div_pos
    · have h := Bint_comb (m := 5) (by norm_num)
      exact_mod_cast h
    · norm_num
  have hsum : 0 < ∑ k ∈ range (numTypes hm + 1), Bk hm k * (Nat.stirlingSecond 4 k : ℝ) := by
    apply sum_pos' (fun k _ => mul_nonneg (hb k) (by positivity))
    refine ⟨4, ?_, ?_⟩
    · rw [numTypes_eq, mem_range]
      norm_num
    · rw [Nat.stirlingSecond_self]
      simpa using hp
  have hN : 0 < numer hm 4 := by
    rw [prop32_stirling_form hm (by norm_num : 0 < (4 : ℕ))]
    exact mul_pos (by positivity) hsum
  have h := prop_small_m (n := 4) (m := 5) (by norm_num) (by norm_num) (by norm_num)
  have hden : (0 : ℝ) < ((2 ^ 4 : ℕ).descFactorial 5 : ℝ) := by
    rw [show (2 ^ 4 : ℕ).descFactorial 5 = 524160 from rfl]
    norm_num
  have hpos : 0 < tG 4 5 (by norm_num) - completeCost 5 := by
    rw [h]
    exact div_pos hN hden
  linarith

end GradientKey.Concrete
