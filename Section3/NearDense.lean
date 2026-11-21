import NearBall
import Counting

/-!
# Proposition 3.5 (`prop:near-dense`)

First formula: if `n ≥ 3` and `m = 2^n - n - 1`, then `t_{n,m}(G) - C(m) = 2^n / (m · C(2^n, n+1))`.
-/

noncomputable section

namespace GradientKey.Concrete

open Finset

variable {n m : ℕ}

theorem ite_exists_ball (hn : 2 ≤ n) (M : Finset (Word n)) :
    (if ∃ c, M = ball c then 1 else 0 : ℕ) = ∑ c : Word n, if M = ball c then 1 else 0 := by
  have hinj := ball_injective (ι := (univ : Finset (Fin n))) (by
    rw [Fintype.card_coe, card_univ, Fintype.card_fin]; exact hn)
  by_cases h : ∃ c, M = ball c
  · obtain ⟨c, hc⟩ := h
    rw [if_pos ⟨c, hc⟩, Finset.sum_eq_single c]
    · simp [hc]
    · intro c' _ hc'
      rw [if_neg]
      intro h'
      exact hc' (hinj (h'.symm.trans hc))
    · simp
  · rw [if_neg h]
    symm
    apply Finset.sum_eq_zero
    intro c _
    rw [if_neg (fun h' => h ⟨c, h'⟩)]

/-- The number of tables whose missing words form a ball is `2^n · m!`. -/
theorem sum_ball_tables (hn : 2 ≤ n) (hm : m + n + 1 = 2 ^ n) :
    (∑ A : ValidTable n m, (if ∃ c, missing A.1 univ univ = ball c then 1 else 0 : ℕ)) =
      2 ^ n * m.factorial := by
  simp_rw [ite_exists_ball hn]
  rw [Finset.sum_comm]
  have : ∀ c : Word n, (∑ A : ValidTable n m, if missing A.1 univ univ = ball c then 1 else 0) =
      m.factorial := by
    intro c
    rw [Finset.sum_boole]
    have := card_missing_eq (m := m) (ball c) (by
      rw [card_ball, Fintype.card_coe, card_univ, Fintype.card_fin]; omega)
    exact_mod_cast this
  rw [Finset.sum_congr rfl (fun c _ => this c), Finset.sum_const, card_univ, card_word, smul_eq_mul]

/-- **Proposition 3.5**, first formula. -/
theorem prop_near_dense_one (hn3 : 3 ≤ n) (hm : m + n + 1 = 2 ^ n) :
    tG n m (by omega) - completeCost m =
      (2 ^ n : ℝ) / ((m : ℝ) * ((2 ^ n).choose (n + 1) : ℕ)) := by
  have hn : 0 < n := by omega
  have hkk := le_two_pow_pred n (by omega)
  have hpk := two_pow_pred n (by omega)
  have hm2 : 2 ≤ m := by omega
  rw [tG_sub_completeCost hn hm2 (by omega)]
  have hD : ∀ A : ValidTable n m, ((totalDepth A.1 hn univ : ℝ) - cdepth m) =
      ((if ∃ c, missing A.1 univ univ = ball c then 1 else 0 : ℕ) : ℝ) := by
    intro A
    have hcm := card_missing A.1 A.2 univ univ (fun _ _ _ _ r hr => absurd (mem_univ r) hr)
    rw [card_univ, card_univ, Fintype.card_fin, Fintype.card_fin] at hcm
    have := near_ball A.1 A.2 hn n hn3 univ univ (by simp) (fun _ _ _ _ r hr => absurd (mem_univ r) hr)
      (by omega)
    rw [this, card_univ, Fintype.card_fin]
    push_cast
    ring
  rw [Finset.sum_congr rfl (fun A _ => hD A), ← Nat.cast_sum, sum_ball_tables (by omega) hm,
    card_valid, Nat.descFactorial_eq_factorial_mul_choose]
  have hch : (2 ^ n).choose m = (2 ^ n).choose (n + 1) := by
    rw [← hm, show m + n + 1 = m + (n + 1) by ring, Nat.choose_symm_add]
  rw [hch]
  have hf : (m.factorial : ℝ) ≠ 0 := by exact_mod_cast (Nat.factorial_pos m).ne'
  push_cast
  field_simp

end GradientKey.Concrete
