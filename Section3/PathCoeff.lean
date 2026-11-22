import Mobius

/-!
# Proposition 3.1: the coefficient `c(λ)`

A type of a set partition of `Fin a` is its vector of multiplicities `u v` = number of blocks of size `v`.
We prove that the sum of the Möbius weights `μ(π)` over the set partitions `π` of `Fin a` of type `u` is
`c(u) = (-1)^(a - p) a! / ∏_v v^(u v) (u v)!`, `p = ∑_v u v` the number of blocks (the article's `c(λ)`).

The proof is a recurrence on `a`: a set partition of `Fin (a+1)` is a set partition of `Fin a` with
a new singleton block or with one block enlarged (`OrderedFinpartition.extendEquiv`), and `c` satisfies
the same recurrence. Products and sums over sizes run over `range B` for a bound `B > a`.
-/

noncomputable section

namespace GradientKey.Concrete

open Finset Classical

/-- `v^y y!`. -/
def fw (v y : ℕ) : ℚ := (v : ℚ) ^ y * (y.factorial : ℚ)

/-- `∏_{v<B} v^(u v) (u v)!`. -/
def Pq (B : ℕ) (u : ℕ → ℕ) : ℚ := ∏ v ∈ range B, fw v (u v)

/-- The number of blocks `∑_{v<B} u v`. -/
def pc (B : ℕ) (u : ℕ → ℕ) : ℕ := ∑ v ∈ range B, u v

/-- The total size `∑_{v<B} v u v`. -/
def wt (B : ℕ) (u : ℕ → ℕ) : ℕ := ∑ v ∈ range B, v * u v

/-- The coefficient `c(u) = (-1)^(a-p) a! / ∏_v v^(u v) (u v)!`. -/
def coefB (B a : ℕ) (u : ℕ → ℕ) : ℚ := (-1 : ℚ) ^ (a - pc B u) * (a.factorial : ℚ) / Pq B u

/-- `u` is the type of a set partition of an `a`-set, with all sizes below `B`. -/
def IsTy (B a : ℕ) (u : ℕ → ℕ) : Prop := u 0 = 0 ∧ (∀ v, B ≤ v → u v = 0) ∧ wt B u = a

theorem fw_ne_zero {v y : ℕ} (h : v ≠ 0 ∨ y = 0) : fw v y ≠ 0 := by
  unfold fw
  apply mul_ne_zero
  · rcases h with h | h
    · exact pow_ne_zero _ (by exact_mod_cast h)
    · simp [h]
  · exact_mod_cast (Nat.factorial_pos y).ne'

theorem Pq_ne_zero {B : ℕ} {u : ℕ → ℕ} (h0 : u 0 = 0) : Pq B u ≠ 0 := by
  apply prod_ne_zero_iff.mpr
  intro v _
  apply fw_ne_zero
  by_cases hv : v = 0
  · right; rw [hv]; exact h0
  · left; exact hv

theorem fw_succ (v y : ℕ) : fw v (y + 1) = fw v y * ((v : ℚ) * (y + 1)) := by
  unfold fw
  rw [Nat.factorial_succ]
  push_cast
  ring

theorem Pq_update {B : ℕ} (u : ℕ → ℕ) {w : ℕ} (hw : w ∈ range B) (x : ℕ) :
    Pq B (Function.update u w x) * fw w (u w) = Pq B u * fw w x := by
  unfold Pq
  have e : (fun v => fw v (Function.update u w x v)) =
      Function.update (fun v => fw v (u v)) w (fw w x) := by
    funext v
    by_cases h : v = w
    · subst h; simp
    · simp [h]
  rw [e, prod_update_of_mem hw, ← mul_prod_erase (range B) (fun v => fw v (u v)) hw,
    sdiff_singleton_eq_erase]
  ring

theorem sum_update_nat {B : ℕ} (f : ℕ → ℕ → ℕ) (u : ℕ → ℕ) {w : ℕ} (hw : w ∈ range B) (x : ℕ) :
    ∑ v ∈ range B, f v (Function.update u w x v) + f w (u w) =
      ∑ v ∈ range B, f v (u v) + f w x := by
  have e : (fun v => f v (Function.update u w x v)) =
      Function.update (fun v => f v (u v)) w (f w x) := by
    funext v
    by_cases h : v = w
    · subst h; simp
    · simp [h]
  rw [e, sum_update_of_mem hw, ← add_sum_erase (range B) (fun v => f v (u v)) hw,
    sdiff_singleton_eq_erase]
  ring

/-- Sizes above the total size do not occur. -/
theorem IsTy.zero_of_lt {B a : ℕ} {u : ℕ → ℕ} (hu : IsTy B a u) {w : ℕ} (hw : a < w) : u w = 0 := by
  by_cases hB : B ≤ w
  · exact hu.2.1 w hB
  · have hle : w * u w ≤ wt B u :=
      single_le_sum (f := fun v => v * u v) (fun _ _ => Nat.zero_le _)
        (mem_range.mpr (by omega))
    rw [hu.2.2] at hle
    by_contra h
    have : w ≤ w * u w := Nat.le_mul_of_pos_right w (Nat.pos_of_ne_zero h)
    omega

/-! ### The first recurrence term: a new singleton block -/

/-- Removing a block of size `1`. -/
def rem1 (u : ℕ → ℕ) : ℕ → ℕ := Function.update u 1 (u 1 - 1)

theorem coef_term1 {B a : ℕ} {u : ℕ → ℕ} (hB : a + 2 ≤ B) (hu : IsTy B (a + 1) u) (h1 : 1 ≤ u 1) :
    coefB B a (rem1 u) = coefB B (a + 1) u * (u 1 : ℚ) / (a + 1) := by
  have h1B : 1 ∈ range B := mem_range.mpr (by omega)
  have hP := Pq_update u h1B (u 1 - 1)
  have hu1 : u 1 = (u 1 - 1) + 1 := by omega
  have hf : fw 1 (u 1) = fw 1 (u 1 - 1) * (u 1 : ℚ) := by
    conv_lhs => rw [hu1]
    rw [fw_succ]
    push_cast [Nat.cast_sub h1]
    ring
  have hp := sum_update_nat (B := B) (fun _ y => y) u h1B (u 1 - 1)
  beta_reduce at hp
  have hpc : pc B (rem1 u) + 1 = pc B u := by unfold pc rem1; omega
  have hexp : a - pc B (rem1 u) = a + 1 - pc B u := by omega
  have hne : fw 1 (u 1 - 1) ≠ 0 := fw_ne_zero (Or.inl one_ne_zero)
  have hPu : Pq B u ≠ 0 := Pq_ne_zero hu.1
  have hu1q : (u 1 : ℚ) ≠ 0 := by exact_mod_cast (show u 1 ≠ 0 by omega)
  have hPr : Pq B (rem1 u) = Pq B u / (u 1 : ℚ) := by
    unfold rem1
    rw [hf] at hP
    field_simp
    have := hP
    field_simp at this
    linarith [this]
  unfold coefB
  rw [hexp, hPr, Nat.factorial_succ]
  push_cast
  field_simp

/-! ### The second recurrence term: an enlarged block -/

/-- Replacing a block of size `v+1` by a block of size `v`. -/
def remv (u : ℕ → ℕ) (v : ℕ) : ℕ → ℕ :=
  Function.update (Function.update u v (u v + 1)) (v + 1) (u (v + 1) - 1)

theorem pc_lt_wt {B a : ℕ} {u : ℕ → ℕ} (hu : IsTy B (a + 1) u) {v : ℕ} (hv1 : 1 ≤ v)
    (hvB : v + 1 < B) (h : 1 ≤ u (v + 1)) : pc B u + 1 ≤ a + 1 := by
  rw [← hu.2.2]
  unfold pc wt
  have hmem : v + 1 ∈ range B := mem_range.mpr hvB
  have key : ∀ w ∈ range B, u w + (if w = v + 1 then 1 else 0) ≤ w * u w := by
    intro w _
    by_cases hw0 : w = 0
    · subst hw0; simp [hu.1]
    · split_ifs with hw
      · subst hw
        have : 2 * u (v + 1) ≤ (v + 1) * u (v + 1) := Nat.mul_le_mul_right _ (by omega)
        omega
      · have : 1 * u w ≤ w * u w := Nat.mul_le_mul_right _ (by omega)
        omega
  have := sum_le_sum key
  rw [sum_add_distrib, sum_ite_eq' (range B) (v + 1), if_pos hmem] at this
  exact this

theorem coef_term2 {B a : ℕ} {u : ℕ → ℕ} (hB : a + 2 ≤ B) (hu : IsTy B (a + 1) u) {v : ℕ}
    (hv1 : 1 ≤ v) (hva : v ≤ a) (h : 1 ≤ u (v + 1)) :
    -(v : ℚ) * ((u v : ℚ) + 1) * coefB B a (remv u v) =
      coefB B (a + 1) u * (((v : ℚ) + 1) * (u (v + 1) : ℚ)) / (a + 1) := by
  have hvB : v ∈ range B := mem_range.mpr (by omega)
  have hv1B : v + 1 ∈ range B := mem_range.mpr (by omega)
  set u1 := Function.update u v (u v + 1) with hu1def
  have hu1v1 : u1 (v + 1) = u (v + 1) := by simp [u1]
  have hP1 := Pq_update u hvB (u v + 1)
  rw [fw_succ] at hP1
  have hP2 := Pq_update u1 hv1B (u (v + 1) - 1)
  rw [hu1v1] at hP2
  have hy : u (v + 1) = (u (v + 1) - 1) + 1 := by omega
  have hf : fw (v + 1) (u (v + 1)) = fw (v + 1) (u (v + 1) - 1) * (((v : ℚ) + 1) * (u (v + 1) : ℚ)) := by
    conv_lhs => rw [hy]
    rw [fw_succ]
    push_cast [Nat.cast_sub h]
    ring
  rw [hf] at hP2
  have hne1 : fw v (u v) ≠ 0 := fw_ne_zero (Or.inl (by omega))
  have hne2 : fw (v + 1) (u (v + 1) - 1) ≠ 0 := fw_ne_zero (Or.inl (by omega))
  have hPu : Pq B u ≠ 0 := Pq_ne_zero hu.1
  have hvq : (v : ℚ) ≠ 0 := by exact_mod_cast (show v ≠ 0 by omega)
  have hyq : (u (v + 1) : ℚ) ≠ 0 := by exact_mod_cast (show u (v + 1) ≠ 0 by omega)
  have hPr : Pq B (remv u v) =
      Pq B u * ((v : ℚ) * ((u v : ℚ) + 1)) / (((v : ℚ) + 1) * (u (v + 1) : ℚ)) := by
    have e1 : Pq B u1 = Pq B u * ((v : ℚ) * ((u v : ℚ) + 1)) := by
      have := hP1
      field_simp at this ⊢
      linarith [this]
    unfold remv
    rw [← hu1def]
    rw [e1] at hP2
    have hv1q : (v : ℚ) + 1 ≠ 0 := by positivity
    field_simp
    have := hP2
    field_simp at this
    linarith [this]
  -- number of blocks
  have hp1 := sum_update_nat (B := B) (fun _ y => y) u hvB (u v + 1)
  have hp2 := sum_update_nat (B := B) (fun _ y => y) u1 hv1B (u (v + 1) - 1)
  beta_reduce at hp1 hp2
  rw [← hu1def] at hp1
  rw [hu1v1] at hp2
  have hpc : pc B (remv u v) = pc B u := by
    unfold pc remv
    rw [← hu1def]
    omega
  have hpa := pc_lt_wt hu hv1 (by omega) h
  have hexp : a + 1 - pc B u = (a - pc B u) + 1 := by omega
  unfold coefB
  rw [hpc, hexp, hPr, pow_succ, Nat.factorial_succ]
  push_cast
  have hv1q : (v : ℚ) + 1 ≠ 0 := by positivity
  have huq : (u v : ℚ) + 1 ≠ 0 := by positivity
  field_simp

/-- **Recurrence for `c`.** -/
theorem coef_rec {B a : ℕ} {u : ℕ → ℕ} (hB : a + 2 ≤ B) (hu : IsTy B (a + 1) u) :
    coefB B (a + 1) u =
      (if 1 ≤ u 1 then coefB B a (rem1 u) else 0) +
        ∑ t ∈ range a, (if 1 ≤ u (t + 2) then
          -((t : ℚ) + 1) * ((u (t + 1) : ℚ) + 1) * coefB B a (remv u (t + 1)) else 0) := by
  have e1 : (if 1 ≤ u 1 then coefB B a (rem1 u) else 0) = coefB B (a + 1) u * (u 1 : ℚ) / (a + 1) := by
    split_ifs with h1
    · exact coef_term1 hB hu h1
    · have : u 1 = 0 := by omega
      simp [this]
  have e2 : ∀ t ∈ range a, (if 1 ≤ u (t + 2) then
      -((t : ℚ) + 1) * ((u (t + 1) : ℚ) + 1) * coefB B a (remv u (t + 1)) else 0) =
        coefB B (a + 1) u * ((((t + 1 : ℕ) : ℚ) + 1) * (u (t + 2) : ℚ)) / (a + 1) := by
    intro t ht
    split_ifs with h2
    · have := coef_term2 hB hu (v := t + 1) (by omega) (by simp at ht; omega) h2
      push_cast at this ⊢
      exact this
    · have : u (t + 2) = 0 := by omega
      simp [this]
  -- `u 1 + ∑_{t<a} (t+2) u (t+2) = a + 1`
  have hsum : (u 1 : ℚ) + ∑ t ∈ range a, ((((t + 1 : ℕ) : ℚ) + 1) * (u (t + 2) : ℚ)) = a + 1 := by
    have hw := hu.2.2
    unfold wt at hw
    have hsub : ∑ v ∈ range B, v * u v = ∑ v ∈ range (a + 2), v * u v := by
      symm
      apply sum_subset (range_mono hB)
      intro w hwB hw2
      simp only [mem_range, not_lt] at hw2
      rw [hu.zero_of_lt (by omega : a + 1 < w), mul_zero]
    rw [hsub, sum_range_succ', sum_range_succ'] at hw
    have hq := congrArg (fun x : ℕ => (x : ℚ)) hw
    push_cast at hq
    rw [← hq]
    have : ∀ t ∈ range a, ((((t + 1 : ℕ) : ℚ) + 1) * (u (t + 2) : ℚ)) =
        ((t : ℚ) + 1 + 1) * (u (t + 1 + 1) : ℚ) := by
      intro t _; push_cast; ring_nf
    rw [sum_congr rfl this]
    ring
  rw [e1, sum_congr rfl e2, ← sum_div, ← mul_sum, ← add_div, ← mul_add, hsum]
  have : (a : ℚ) + 1 ≠ 0 := by positivity
  field_simp

end GradientKey.Concrete
