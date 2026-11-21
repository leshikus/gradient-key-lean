import NearTwoCount
import NearDense

/-!
# Proposition 3.5, second formula

If `n ≥ 4` and `m = 2^n - n - 2`, then `t_{n,m}(G) - C(m) = 2^{n-2} (3^n - 2n - 1) / (m · C(2^n, n+2))`.
-/

noncomputable section

namespace GradientKey.Concrete

open Finset

variable {n m : ℕ}

/-- The index of a set with excess `1`: the row `j`, the side `b`, the centre `c`. -/
abbrev Idx (n : ℕ) := Σ j : Fin n, Bool × (((univ : Finset (Fin n)).erase j) → Bool)

open Classical in
/-- The sets of `n + 2` missing words with excess `1`. -/
def Good (n : ℕ) (hn : 0 < n) : Finset (Finset (Word n)) :=
  (univ : Finset (Finset (Word n))).filter (fun R => R.card = n + 2 ∧ QR R hn)

open Classical in
theorem card_Good_sum (hn : 0 < n) (hn4 : 4 ≤ n) :
    (Good n hn).card = ∑ x : Idx n, (Yset x.1 x.2.1 x.2.2).card := by
  rw [← card_sigma]
  symm
  apply card_bij (fun p _ => phiR p.1.1 p.1.2.1 p.1.2.2 p.2)
  · rintro ⟨⟨j, b, c⟩, Y⟩ hp
    rw [mem_sigma] at hp
    obtain ⟨hY2, hYb, -⟩ := mem_Yset.mp hp.2
    simp only [Good, mem_filter, mem_univ, true_and]
    exact ⟨card_phi j b c Y (by omega) hYb hY2, QR_phi hn hn4 j b c Y hp.2⟩
  · rintro ⟨⟨j, b, c⟩, Y⟩ hp ⟨⟨j', b', c'⟩, Y'⟩ hp' he
    rw [mem_sigma] at hp hp'
    obtain ⟨rfl, rfl, hc, rfl⟩ := phi_inj hn hn4 hp.2 hp'.2 he
    have := eq_of_heq hc
    simp only at this
    subst this
    rfl
  · intro R hR
    simp only [Good, mem_filter, mem_univ, true_and] at hR
    obtain ⟨b, c, hRphi, hY⟩ := phi_of_QR hn hn4 R hR.1 hR.2
    exact ⟨⟨⟨gR R hn, b, c⟩, _⟩, mem_sigma.mpr ⟨mem_univ _, hY⟩, hRphi.symm⟩

/-- `4 ∑_{t<n} (3^t - 1)/2 + 2n + 1 = 3^n`. -/
theorem sum_half_pow (n : ℕ) : 4 * (∑ t ∈ range n, (3 ^ t - 1) / 2) + 2 * n + 1 = 3 ^ n := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [sum_range_succ, pow_succ]
    have hodd : 2 * ((3 ^ n - 1) / 2) + 1 = 3 ^ n := by
      have : 3 ^ n % 2 = 1 := Nat.pow_mod 3 n 2 ▸ by simp
      have : 1 ≤ 3 ^ n := Nat.one_le_pow _ _ (by norm_num)
      omega
    omega

theorem four_mul_card_Good (hn : 0 < n) (hn4 : 4 ≤ n) :
    4 * (Good n hn).card = 2 ^ n * (3 ^ n - 2 * n - 1) := by
  rw [card_Good_sum hn hn4, Fintype.sum_sigma]
  have hY : ∀ (j : Fin n) (x : Bool × (((univ : Finset (Fin n)).erase j) → Bool)),
      (Yset j x.1 x.2).card = (3 ^ (n - 1 - j.val) - 1) / 2 := by
    intro j x
    have := card_Yset j x.1 x.2
    omega
  simp only [hY, sum_const, card_univ, Fintype.card_prod, Fintype.card_bool, Fintype.card_fun,
    Fintype.card_coe, card_erase_of_mem (mem_univ _), Fintype.card_fin, smul_eq_mul]
  rw [← mul_sum, Fin.sum_univ_eq_sum_range (fun j => (3 ^ (n - 1 - j) - 1) / 2) n,
    sum_range_reflect (fun t => (3 ^ t - 1) / 2) n]
  have h := sum_half_pow n
  have hp : 2 * 2 ^ (n - 1) = 2 ^ n := by rw [← pow_succ']; congr 1; omega
  rw [← mul_assoc, hp]
  have : 3 ^ n - 2 * n - 1 = 4 * ∑ t ∈ range n, (3 ^ t - 1) / 2 := by omega
  rw [this]; ring

open Classical in
/-- The number of tables with excess `1` is `|Good| · m!`. -/
theorem card_tables_good (hn : 0 < n) (hm : m + n + 2 = 2 ^ n) :
    (univ.filter (fun A : ValidTable n m => QR (missing A.1 univ univ) hn)).card =
      (Good n hn).card * m.factorial := by
  have hmaps : ∀ A ∈ univ.filter (fun A : ValidTable n m => QR (missing A.1 univ univ) hn),
      missing A.1 univ univ ∈ Good n hn := by
    intro A hA
    have hcm := card_missing A.1 A.2 univ univ (fun _ _ _ _ r hr => absurd (mem_univ r) hr)
    rw [card_univ, card_univ, Fintype.card_fin, Fintype.card_fin] at hcm
    simp only [Good, mem_filter, mem_univ, true_and] at hA ⊢
    exact ⟨by omega, hA⟩
  rw [card_eq_sum_card_fiberwise hmaps]
  apply sum_const_nat
  intro R hR
  simp only [Good, mem_filter, mem_univ, true_and] at hR
  rw [filter_filter]
  have : (univ.filter (fun A : ValidTable n m =>
      QR (missing A.1 univ univ) hn ∧ missing A.1 univ univ = R)) =
      univ.filter (fun A : ValidTable n m => missing A.1 univ univ = R) := by
    congr 1; funext A; apply propext
    constructor
    · exact fun h => h.2
    · intro h; exact ⟨h ▸ hR.2, h⟩
  rw [this]
  convert card_missing_eq (m := m) R (by rw [hR.1]; omega) using 2

/-- **Proposition 3.5**, second formula. -/
theorem prop_near_dense_two (hn4 : 4 ≤ n) (hm : m + n + 2 = 2 ^ n) :
    tG n m (by omega) - completeCost m =
      ((2 ^ (n - 2) * (3 ^ n - 2 * n - 1) : ℕ) : ℝ) / ((m : ℝ) * ((2 ^ n).choose (n + 2) : ℕ)) := by
  classical
  have hn : 0 < n := by omega
  have hkk := le_two_pow_pred n (by omega)
  have hpk := two_pow_pred n (by omega)
  have hm2 : 2 ≤ m := by have := le_two_pow_sub_two n hn4; omega
  rw [tG_sub_completeCost hn hm2 (by omega)]
  have hD : ∀ A : ValidTable n m, ((totalDepth A.1 hn univ : ℝ) - cdepth m) =
      ((if QR (missing A.1 univ univ) hn then 1 else 0 : ℕ) : ℝ) := by
    intro A
    have hS : AgreeOff A.1 univ univ := fun _ _ _ _ r hr => absurd (mem_univ r) hr
    have hcm := card_missing A.1 A.2 univ univ hS
    rw [card_univ, card_univ, Fintype.card_fin, Fintype.card_fin] at hcm
    have hR : (missing A.1 univ univ).card = n + 2 := by omega
    have := near_two A.1 A.2 hn n hn4 univ univ (by simp) hS hR
    rw [this, card_univ, Fintype.card_fin]
    by_cases hq : QR (missing A.1 univ univ) hn
    · rw [if_pos ((twoBall_root A.1 A.2 hn hn4 hR).mpr hq), if_pos hq]; push_cast; ring
    · rw [if_neg (fun h => hq ((twoBall_root A.1 A.2 hn hn4 hR).mp h)), if_neg hq]; push_cast; ring
  rw [Finset.sum_congr rfl (fun A _ => hD A), ← Nat.cast_sum, Finset.sum_boole,
    card_tables_good hn hm, card_valid, Nat.descFactorial_eq_factorial_mul_choose]
  have hch : (2 ^ n).choose m = (2 ^ n).choose (n + 2) := by
    rw [← hm, show m + n + 2 = m + (n + 2) by ring, Nat.choose_symm_add]
  rw [hch]
  have h4 := four_mul_card_Good hn hn4
  have hG : (Good n hn).card = 2 ^ (n - 2) * (3 ^ n - 2 * n - 1) := by
    have hp : 2 ^ n = 4 * 2 ^ (n - 2) := by
      rw [show (4 : ℕ) = 2 ^ 2 by norm_num, ← pow_add]; congr 1; omega
    rw [hp] at h4
    linarith
  rw [hG]
  have hf : (m.factorial : ℝ) ≠ 0 := by exact_mod_cast (Nat.factorial_pos m).ne'
  push_cast
  field_simp

end GradientKey.Concrete
