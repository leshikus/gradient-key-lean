import Lemma43

/-!
# Theorem 4.4

`tG n m hn` is the article's `t_{n,m}(G)`: the average over the tables
`A ∈ 𝒜_{n,m}` (binary `n × m`, distinct columns) of the cost
`L̄(G(A)) = (1/m) ∑_j L_j`, where `L_j` is the number of depths `i ≥ 0` at which
the path of column `j` in the greedy tree `G(A)` has a fork (`s_i ≥ 2`).
The greedy rule is `Concrete.greedyRow`: the first row of largest quality.

`theorem_4_4` states the displayed bound and (a)–(c) for all `2 ≤ m ≤ 2^n`;
its only hypotheses are `2 ≤ m`, `m ≤ 2^n`, and `n ≥ 2ℓ - 2` in (c).
-/

noncomputable section

namespace GradientKey.Concrete

open Finset

variable {n m : ℕ}

/-- `L_j`: the depth of the leaf of column `j` in `G(A)`, i.e. the number of
depths `i` with `s_i ≥ 2`. -/
def leafDepth (A : Table n m) (hn : 0 < n) (j : Fin m) : ℕ :=
  Set.ncard {i : ℕ | 2 ≤ (candidateAt A j hn i).card}

/-- The cost `L̄(G(A)) = (1/m) ∑_j L_j`. -/
def cost (A : Table n m) (hn : 0 < n) : ℝ :=
  (∑ j : Fin m, (leafDepth A hn j : ℝ)) / (m : ℝ)

/-- `t_{n,m}(G)`: the average cost over `𝒜_{n,m}`. -/
def tG (n m : ℕ) (hn : 0 < n) : ℝ :=
  (∑ A : ValidTable n m, cost A.1 hn) / (Fintype.card (ValidTable n m) : ℝ)

theorem leafDepth_eq_pathDepth (A : Table n m) (hA : DistinctColumns A) (hn : 0 < n)
    (j : Fin m) : (leafDepth A hn j : ℝ) = pathDepth A j hn := by
  unfold leafDepth pathDepth
  have hset : {i : ℕ | 2 ≤ (candidateAt A j hn i).card} =
      ↑((Finset.range n).filter (fun i => 2 ≤ (candidateAt A j hn i).card)) := by
    ext i
    simp only [Set.mem_setOf_eq, Finset.coe_filter, Finset.mem_range]
    constructor
    · intro h
      refine ⟨?_, h⟩
      by_contra hni
      rw [p1_terminated_after_n A hA j hn i (by omega)] at h
      simp at h
    · exact fun h => h.2
  rw [hset, Set.ncard_coe_finset]

/-- The sample space of (table, column) pairs is nonempty for `2 ≤ m ≤ 2^n`:
column `j` is the binary expansion of `j`. -/
theorem sample_nonempty (hm : 2 ≤ m) (hsize : m ≤ 2 ^ n) : Nonempty (Sample n m) := by
  let A : Table n m := fun r j => Nat.testBit j.val r.val
  have hA : DistinctColumns A := by
    intro j k hjk
    apply Fin.ext
    apply Nat.eq_of_testBit_eq
    intro b
    by_cases hb : b < n
    · exact congrFun hjk ⟨b, hb⟩
    · have hpow : 2 ^ n ≤ 2 ^ b := Nat.pow_le_pow_right (by norm_num) (by omega)
      rw [Nat.testBit_eq_false_of_lt (lt_of_lt_of_le (lt_of_lt_of_le j.2 hsize) hpow),
        Nat.testBit_eq_false_of_lt (lt_of_lt_of_le (lt_of_lt_of_le k.2 hsize) hpow)]
  exact ⟨(⟨A, hA⟩, ⟨0, by omega⟩)⟩

theorem n_pos (hm : 2 ≤ m) (hsize : m ≤ 2 ^ n) : 0 < n := by
  rcases Nat.eq_zero_or_pos n with h | h
  · subst h; simp at hsize; omega
  · exact h

/-- The expected path length over the uniform (table, column) sample is
`t_{n,m}(G)`. -/
theorem expectedDepth_eq_tG (hn : 0 < n) [Nonempty (Sample n m)] :
    (p1_finitePathData (m := m) hn).expectedDepth = tG n m hn := by
  have hm : (0 : ℝ) < m := by
    have : 0 < m := Fin.pos (Classical.arbitrary (Sample n m)).2
    exact_mod_cast this
  unfold FinitePathData.expectedDepth finiteAverage tG cost
  change (∑ ω : Sample n m, sampleDepth hn ω) / _ = _
  rw [sum_sample]
  have hL : ∀ A : ValidTable n m, (∑ j : Fin m, sampleDepth hn (A, j)) =
      ∑ j : Fin m, (leafDepth A.1 hn j : ℝ) := by
    intro A
    apply Finset.sum_congr rfl
    intro j _
    exact (leafDepth_eq_pathDepth A.1 A.2 hn j).symm
  simp only [hL]
  rw [Fintype.card_prod, Fintype.card_fin, Nat.cast_mul, ← Finset.sum_div]
  field_simp

/-- The bound displayed in Theorem 4.4, with `2^{i-ℓ}` written as `2^i/2^ℓ`. -/
def displayedBound (n m : ℕ) : ℝ :=
  (Nat.log 2 m : ℝ) - 1 + (m : ℝ) / (2 : ℝ) ^ (Nat.log 2 m) +
    ∑ i ∈ Finset.range (Nat.log 2 m),
      (2 : ℝ) ^ i / (2 : ℝ) ^ (Nat.log 2 m) *
        min ((n : ℝ) / ((n : ℝ) - (i : ℝ)))
          (2 + 2 * Real.log (2 * (n : ℝ) / ((n : ℝ) - (i : ℝ))))

/-- **Theorem 4.4.** Let `2 ≤ m ≤ 2^n` and `ℓ = ⌊log₂ m⌋`. Then
`t_{n,m}(G) ≤ ℓ - 1 + m 2^{-ℓ} + ∑_{i<ℓ} 2^{i-ℓ} min{n/(n-i), 2 + 2 ln(2n/(n-i))}`, and
(a) `t_{n,m}(G) < log₂ m + 2 + 2 ln(2ℓ)`;
(b) `t_{n,m}(G) < log₂ m + 1 + (ℓ-1)/(n-ℓ+1)`;
(c) `t_{n,m}(G) < log₂ m + 2` if `n ≥ 2ℓ - 2`. -/
theorem theorem_4_4 (n m : ℕ) (hm : 2 ≤ m) (hsize : m ≤ 2 ^ n) :
    tG n m (n_pos hm hsize) ≤ displayedBound n m ∧
    tG n m (n_pos hm hsize) <
      Real.logb 2 (m : ℝ) + 2 + 2 * Real.log (2 * (Nat.log 2 m : ℝ)) ∧
    tG n m (n_pos hm hsize) <
      Real.logb 2 (m : ℝ) + 1 +
        ((Nat.log 2 m : ℝ) - 1) / ((n : ℝ) - (Nat.log 2 m : ℝ) + 1) ∧
    (2 * Nat.log 2 m - 2 ≤ n → tG n m (n_pos hm hsize) < Real.logb 2 (m : ℝ) + 2) := by
  obtain ⟨k, rfl⟩ : ∃ k, n = k + 1 := ⟨n - 1, by have := n_pos hm hsize; omega⟩
  haveI : Nonempty (Sample (k + 1) m) := sample_nonempty hm hsize
  set hn := n_pos hm hsize
  have hmain := theorem_4_4_from_finite_paths (k + 1) m hm hsize
    (p1_finitePathData (m := m) hn)
    (fun i => concrete_expectedExcess_succ hn i)
    (fun i hi => expectedImbalance_le_rows hn i hi)
    (fun i hi hp => expectedImbalance_le_log hn i hi hp)
  rw [expectedDepth_eq_tG hn] at hmain
  exact hmain

end GradientKey.Concrete
