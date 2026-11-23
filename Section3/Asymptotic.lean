import SmallM

/-!
# Corollary 3.4 (`cor:exp`)

For fixed `m ≥ 4`, `t_{n,m}(G) - C(m) = A_m r_m^n (1 + O_m(θ_m^n))` as `n → ∞`, with `A_m = B_J / J!`,
`r_m = J / 2^{m-1}` and `θ_m = (J-1)/J`. Stated with explicit constants: there are `C` and `N₀` with
`|t_{n,m}(G) - C(m) - A_m r_m^n| ≤ C · A_m r_m^n θ_m^n` for all `n ≥ N₀`. For `m ≤ 3` the excess is `0`.
-/

noncomputable section

open Classical

namespace GradientKey.Concrete

open Finset

variable {n m : ℕ}

/-- Weierstrass: `∏ (1 - a_i) ≥ 1 - ∑ a_i` for `0 ≤ a_i ≤ 1`. -/
theorem one_sub_sum_le_prod (a : ℕ → ℝ) (k : ℕ) (h : ∀ i ∈ range k, 0 ≤ a i ∧ a i ≤ 1) :
    1 - ∑ i ∈ range k, a i ≤ ∏ i ∈ range k, (1 - a i) := by
  induction k with
  | zero => simp
  | succ k ih =>
    rw [sum_range_succ, prod_range_succ]
    have ih' := ih (fun i hi => h i (mem_range.mpr (Nat.lt_succ_of_lt (mem_range.mp hi))))
    obtain ⟨h0, h1⟩ := h k (mem_range.mpr (Nat.lt_succ_self k))
    have hs : 0 ≤ ∑ i ∈ range k, a i := sum_nonneg (fun i hi => (h i (mem_range.mpr
      (Nat.lt_succ_of_lt (mem_range.mp hi)))).1)
    nlinarith

/-- Bounds on `(x)_m` for `x = 2^n ≥ 2m`. -/
theorem descFactorial_bounds (hm : 0 < m) (hx : 2 * m ≤ 2 ^ n) :
    ((2 : ℝ) ^ n) ^ m / 2 ^ m ≤ ((2 ^ n).descFactorial m : ℝ) ∧
      ((2 : ℝ) ^ n) ^ m - ((2 ^ n).descFactorial m : ℝ) ≤ ((2 : ℝ) ^ n) ^ m * (m ^ 2 / 2 ^ n) := by
  set x : ℝ := (2 : ℝ) ^ n with hxdef
  have hxpos : 0 < x := by positivity
  have hxm : (2 * m : ℝ) ≤ x := by rw [hxdef]; exact_mod_cast hx
  have hD : ((2 ^ n).descFactorial m : ℝ) = ∏ i ∈ range m, (x - i) := by
    rw [Nat.descFactorial_eq_prod_range, Nat.cast_prod]
    apply prod_congr rfl; intro i hi
    rw [Nat.cast_sub (by have := mem_range.mp hi; omega)]
    push_cast; rfl
  have hD' : ∏ i ∈ range m, (x - i) = x ^ m * ∏ i ∈ range m, (1 - (i : ℝ) / x) := by
    rw [show x ^ m = ∏ _i ∈ range m, x by rw [prod_const, card_range], ← prod_mul_distrib]
    apply prod_congr rfl; intro i _; field_simp
  constructor
  · rw [hD, div_eq_mul_inv, ← inv_pow, ← mul_pow,
      show (x * 2⁻¹) ^ m = ∏ _i ∈ range m, (x * 2⁻¹) by rw [prod_const, card_range]]
    gcongr with i hi
    · have : (i : ℝ) ≤ m := by exact_mod_cast (mem_range.mp hi).le
      linarith
  · rw [hD, hD']
    have hw := one_sub_sum_le_prod (fun i => (i : ℝ) / x) m (by
      intro i hi
      have : (i : ℝ) ≤ m := by exact_mod_cast (mem_range.mp hi).le
      exact ⟨by positivity, by rw [div_le_one hxpos]; linarith⟩)
    have hsum : ∑ i ∈ range m, (i : ℝ) / x ≤ m ^ 2 / x := by
      rw [← sum_div]
      apply div_le_div_of_nonneg_right _ hxpos.le
      calc ∑ i ∈ range m, (i : ℝ) ≤ ∑ i ∈ range m, (m : ℝ) :=
            sum_le_sum (fun i hi => by exact_mod_cast (mem_range.mp hi).le)
        _ = m ^ 2 := by rw [sum_const, card_range, nsmul_eq_mul]; ring
    have hxm' : 0 ≤ x ^ m := by positivity
    nlinarith

/-- `a_j = 0` for `j > J`. -/
theorem coeffA_eq_zero_of_J_lt (hm4 : 4 ≤ m) {j : ℕ} (hj : J hm4 < j) :
    coeffA (by omega : 0 < m) j = 0 := by
  unfold coeffA
  apply sum_eq_zero
  intro k _
  rcases lt_or_ge k j with h | h
  · rw [Nat.choose_eq_zero_of_lt h]; simp
  · unfold Bk; rw [Bint_eq_zero_of_J_lt hm4 (by omega)]; simp

/-- `A_m = B_J / J!`. -/
def Am (hm4 : 4 ≤ m) : ℝ := Bk (by omega : 0 < m) (J hm4) / (J hm4).factorial

/-- `r_m = J / 2^{m-1}`. -/
def rm (hm4 : 4 ≤ m) : ℝ := (J hm4 : ℝ) / 2 ^ (m - 1)

/-- `θ_m = (J - 1) / J`. -/
def θm (hm4 : 4 ≤ m) : ℝ := ((J hm4 : ℝ) - 1) / J hm4

set_option maxHeartbeats 4000000 in
/-- **Corollary 3.4.** For fixed `m ≥ 4`: `A_m > 0`, `0 < r_m < 1`, `0 < θ_m < 1`, and
`t_{n,m}(G) - C(m) = A_m r_m^n (1 + O_m(θ_m^n))`, with explicit `C` and `N₀` depending on `m`. -/
theorem cor_exp (hm4 : 4 ≤ m) :
    0 < Am hm4 ∧ 0 < rm hm4 ∧ rm hm4 < 1 ∧ 0 < θm hm4 ∧ θm hm4 < 1 ∧
      ∃ C N₀ : ℝ, ∀ (n : ℕ) (hn : 0 < n), m ≤ 2 ^ n → N₀ ≤ n →
        |(tG n m hn - completeCost m) - Am hm4 * rm hm4 ^ n| ≤
          C * (Am hm4 * rm hm4 ^ n) * θm hm4 ^ n := by
  have hm : 0 < m := by omega
  obtain ⟨hJ1, hJ2⟩ := J_bounds hm4
  rw [numTypes_eq] at hJ2
  obtain ⟨haJ, hA⟩ := coeffA_J hm4
  have hzero : ∀ j, J hm4 < j → coeffA hm j = 0 := fun j hj => coeffA_eq_zero_of_J_lt hm4 hj
  have hAm : Am hm4 = coeffA hm (J hm4) := by rw [Am, haJ]
  simp only [hAm, rm, θm]
  have hJmem : J hm4 ∈ Icc 1 (numTypes hm) := by rw [numTypes_eq]; exact mem_Icc.mpr ⟨by omega, hJ2.le⟩
  clear haJ hAm
  generalize J hm4 = JJ at *
  set A := coeffA hm JJ with hAdef
  set r : ℝ := (JJ : ℝ) / 2 ^ (m - 1) with hrdef
  set θ : ℝ := ((JJ : ℝ) - 1) / JJ with hθdef
  have hJ3 : (3 : ℝ) ≤ JJ := by have : 3 ≤ JJ := by omega
                                exact_mod_cast this
  have hP : (0 : ℝ) < 2 ^ (m - 1) := by positivity
  have hJP : (JJ : ℝ) < 2 ^ (m - 1) := by exact_mod_cast hJ2
  have hr0 : 0 < r := by rw [hrdef]; positivity
  have hr1 : r < 1 := by rw [hrdef, div_lt_one hP]; exact hJP
  have hθ0 : 0 < θ := by rw [hθdef]; apply div_pos <;> linarith
  have hθ1 : θ < 1 := by rw [hθdef, div_lt_one (by linarith)]; linarith
  have hθh : (1 : ℝ) / 2 ≤ θ := by
    rw [hθdef, div_le_div_iff₀ (by norm_num) (by linarith)]; linarith
  refine ⟨hA, hr0, hr1, hθ0, hθ1, ?_⟩
  set c1 : ℝ := ∑ j ∈ Icc 1 (numTypes hm), |coeffA hm j|
  refine ⟨c1 * 2 ^ m / A + (m : ℝ) ^ 2 * 2 ^ m, (2 * m : ℝ), ?_⟩
  intro n hn hsize hN
  have hx : 2 * m ≤ 2 ^ n := by
    have h1 : 2 * m ≤ n := by exact_mod_cast hN
    have h2 := Nat.lt_two_pow_self (n := n)
    omega
  obtain ⟨hD1, hD2⟩ := descFactorial_bounds hm hx
  set x : ℝ := (2 : ℝ) ^ n with hxdef
  set D : ℝ := ((2 ^ n).descFactorial m : ℝ)
  have hxpos : 0 < x := by positivity
  have hxm : 0 < x ^ m := by positivity
  have hDpos : 0 < D := lt_of_lt_of_le (by positivity) hD1
  rw [prop_small_m (by omega) hsize hn]
  set R : ℝ := numer hm n - A * (2 * JJ : ℝ) ^ n with hRdef
  have hR : |R| ≤ c1 * (2 * ((JJ : ℝ) - 1)) ^ n := by
    have : R = ∑ j ∈ (Icc 1 (numTypes hm)).erase JJ, coeffA hm j * (2 * j : ℝ) ^ n := by
      rw [hRdef, numer, ← sum_erase_add _ _ hJmem]; ring
    rw [this]
    calc |∑ j ∈ (Icc 1 (numTypes hm)).erase JJ, coeffA hm j * (2 * j : ℝ) ^ n|
        ≤ ∑ j ∈ (Icc 1 (numTypes hm)).erase JJ, |coeffA hm j * (2 * j : ℝ) ^ n| := abs_sum_le_sum_abs _ _
      _ ≤ ∑ j ∈ (Icc 1 (numTypes hm)).erase JJ, |coeffA hm j| * (2 * ((JJ : ℝ) - 1)) ^ n := by
          apply sum_le_sum; intro j hj
          rw [abs_mul]
          rcases lt_or_gt_of_ne (ne_of_mem_erase hj) with h | h
          · apply mul_le_mul_of_nonneg_left _ (abs_nonneg _)
            rw [abs_of_nonneg (by positivity)]
            apply pow_le_pow_left₀ (by positivity)
            have : ((j + 1 : ℕ) : ℝ) ≤ JJ := by exact_mod_cast h
            push_cast at this; linarith
          · rw [hzero j h]; simp
      _ ≤ c1 * (2 * ((JJ : ℝ) - 1)) ^ n := by
          rw [← sum_mul]
          apply mul_le_mul_of_nonneg_right _ (pow_nonneg (by linarith) n)
          exact sum_le_sum_of_subset_of_nonneg (erase_subset _ _) (fun _ _ _ => abs_nonneg _)
  have hnum : numer hm n = A * (2 * JJ : ℝ) ^ n + R := by rw [hRdef]; ring
  have hxm2 : x ^ m = 2 ^ n * ((2 : ℝ) ^ (m - 1)) ^ n := by
    rw [hxdef, ← pow_mul, ← pow_mul, ← pow_add]; congr 1
    have : m = (m - 1) + 1 := by omega
    conv_lhs => rw [this]
    ring
  have hArn : A * r ^ n = A * (2 * JJ : ℝ) ^ n / x ^ m := by
    rw [hrdef, div_pow, mul_pow, hxm2]
    field_simp
  have hkey : (2 * ((JJ : ℝ) - 1)) ^ n / x ^ m = r ^ n * θ ^ n := by
    rw [hrdef, hθdef, ← mul_pow, show (JJ : ℝ) / 2 ^ (m - 1) * ((JJ - 1) / JJ) = (JJ - 1) / 2 ^ (m - 1) by
      field_simp]
    rw [div_pow, mul_pow, hxm2]
    field_simp
  rw [hnum]
  show |(A * (2 * JJ : ℝ) ^ n + R) / D - A * r ^ n| ≤ _
  have hsplit : (A * (2 * JJ : ℝ) ^ n + R) / D - A * r ^ n =
      R / D + A * (2 * JJ : ℝ) ^ n * ((x ^ m - D) / (D * x ^ m)) := by
    rw [hArn]; field_simp; ring
  rw [hsplit]
  have hT1 : |R / D| ≤ c1 * 2 ^ m / A * (A * r ^ n) * θ ^ n := by
    rw [abs_div, abs_of_pos hDpos, div_le_iff₀ hDpos]
    calc |R| ≤ c1 * (2 * ((JJ : ℝ) - 1)) ^ n := hR
      _ = c1 * 2 ^ m * (r ^ n * θ ^ n) * (x ^ m / 2 ^ m) := by
          rw [← hkey]; field_simp
      _ ≤ c1 * 2 ^ m * (r ^ n * θ ^ n) * D := by
          apply mul_le_mul_of_nonneg_left hD1 (by positivity)
      _ = c1 * 2 ^ m / A * (A * r ^ n) * θ ^ n * D := by field_simp
  have hT2 : |A * (2 * JJ : ℝ) ^ n * ((x ^ m - D) / (D * x ^ m))| ≤
      (m : ℝ) ^ 2 * 2 ^ m * (A * r ^ n) * θ ^ n := by
    have hnn : 0 ≤ x ^ m - D := by
      have h := Nat.descFactorial_le_pow (2 ^ n) m
      have h' : (D : ℝ) ≤ (((2 ^ n) ^ m : ℕ) : ℝ) := Nat.cast_le.mpr h
      rw [Nat.cast_pow, Nat.cast_pow, Nat.cast_ofNat] at h'
      linarith
    rw [abs_of_nonneg (by positivity)]
    have h2n : (1 / 2 : ℝ) ^ n ≤ θ ^ n := pow_le_pow_left₀ (by norm_num) hθh n
    have hxn : 1 / x = (1 / 2 : ℝ) ^ n := by rw [hxdef, one_div_pow]
    calc A * (2 * JJ : ℝ) ^ n * ((x ^ m - D) / (D * x ^ m))
        ≤ A * (2 * JJ : ℝ) ^ n * ((x ^ m * (m ^ 2 / x)) / (x ^ m / 2 ^ m * x ^ m)) := by
          apply mul_le_mul_of_nonneg_left _ (by positivity)
          apply div_le_div₀ (by positivity) hD2 (by positivity)
          exact mul_le_mul_of_nonneg_right hD1 hxm.le
      _ = (m : ℝ) ^ 2 * 2 ^ m * (A * (2 * JJ : ℝ) ^ n / x ^ m) * (1 / x) := by field_simp
      _ = (m : ℝ) ^ 2 * 2 ^ m * (A * r ^ n) * (1 / 2) ^ n := by rw [← hArn, hxn]
      _ ≤ (m : ℝ) ^ 2 * 2 ^ m * (A * r ^ n) * θ ^ n := by
          apply mul_le_mul_of_nonneg_left h2n (by positivity)
  calc |R / D + A * (2 * JJ : ℝ) ^ n * ((x ^ m - D) / (D * x ^ m))|
      ≤ |R / D| + |A * (2 * JJ : ℝ) ^ n * ((x ^ m - D) / (D * x ^ m))| := abs_add_le _ _
    _ ≤ c1 * 2 ^ m / A * (A * r ^ n) * θ ^ n + (m : ℝ) ^ 2 * 2 ^ m * (A * r ^ n) * θ ^ n :=
        add_le_add hT1 hT2
    _ = (c1 * 2 ^ m / A + (m : ℝ) ^ 2 * 2 ^ m) * (A * r ^ n) * θ ^ n := by ring

/-- For `m ≤ 3` the excess vanishes: `t_{n,m}(G) = C(m)`. -/
theorem excess_small (hm2 : 2 ≤ m) (hm3 : m ≤ 3) (hsize : m ≤ 2 ^ n) (hn : 0 < n) :
    tG n m hn - completeCost m = 0 := by
  rw [prop_small_m hm2 hsize hn]
  unfold numer coeffA Bk
  simp [Bint_small hm2 hm3]

end GradientKey.Concrete
