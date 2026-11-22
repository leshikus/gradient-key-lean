import Theorem44

/-!
# Total depth of the greedy subtree on a candidate set

`candFrom A hn S j i` is the candidate set at depth `i` on the path of column `j` in the subtree of `G(A)`
whose root has candidate set `S`. `totalDepth A hn S` is the sum over `j ∈ S` of the number of forks on
this path. For `S = univ` it is `∑_j L_j`, and it satisfies the recursion of a binary tree.
-/

noncomputable section

namespace GradientKey.Concrete

open Finset

variable {n m : ℕ}

/-- The candidate set at depth `i` below a fork with candidate set `S`. -/
def candFrom (A : Table n m) (hn : 0 < n) (S : Finset (Fin m)) (j : Fin m) (i : ℕ) :
    Finset (Fin m) :=
  (fun T => candidateStep A T j hn)^[i] S

theorem candFrom_zero (A : Table n m) (hn : 0 < n) (S : Finset (Fin m)) (j : Fin m) :
    candFrom A hn S j 0 = S := rfl

theorem candFrom_succ (A : Table n m) (hn : 0 < n) (S : Finset (Fin m)) (j : Fin m) (i : ℕ) :
    candFrom A hn S j (i + 1) = candidateStep A (candFrom A hn S j i) j hn := by
  unfold candFrom
  rw [Function.iterate_succ_apply']

theorem candFrom_succ' (A : Table n m) (hn : 0 < n) (S : Finset (Fin m)) (j : Fin m) (i : ℕ) :
    candFrom A hn S j (i + 1) = candFrom A hn (candidateStep A S j hn) j i := by
  unfold candFrom
  rw [Function.iterate_succ_apply]

theorem candidateAt_eq_candFrom (A : Table n m) (hn : 0 < n) (j : Fin m) (i : ℕ) :
    candidateAt A j hn i = candFrom A hn univ j i := by
  induction i with
  | zero => rfl
  | succ i ih => rw [candFrom_succ, ← ih]; rfl

theorem candFrom_mem (A : Table n m) (hn : 0 < n) (S : Finset (Fin m)) (j : Fin m)
    (hj : j ∈ S) (i : ℕ) : j ∈ candFrom A hn S j i := by
  induction i with
  | zero => exact hj
  | succ i ih => rw [candFrom_succ]; exact p1_step_mem A _ j hn ih

theorem candFrom_subset (A : Table n m) (hn : 0 < n) (S : Finset (Fin m)) (j : Fin m) (i : ℕ) :
    candFrom A hn S j (i + 1) ⊆ candFrom A hn S j i := by
  rw [candFrom_succ]; exact p1_step_subset A _ j hn

/-- A fork at depth `i` below `S` leaves at least `i + 2` columns in `S`. -/
theorem candFrom_fork_bound (A : Table n m) (hA : DistinctColumns A) (hn : 0 < n)
    (S : Finset (Fin m)) (j : Fin m) (hj : j ∈ S) (i : ℕ)
    (h : 2 ≤ (candFrom A hn S j i).card) : (candFrom A hn S j i).card + i ≤ S.card := by
  induction i with
  | zero => simp [candFrom_zero]
  | succ i ih =>
    have hsub := Finset.card_le_card (candFrom_subset A hn S j i)
    have hprev : 2 ≤ (candFrom A hn S j i).card := le_trans h hsub
    have hlt := p1_greedy_step_card_lt A hA (candFrom A hn S j i) j hn
      (candFrom_mem A hn S j hj i) hprev
    rw [candFrom_succ] at h ⊢
    have := ih hprev
    omega

/-- Number of forks among the first `N` depths below `S` on the path of `j`. -/
def forksN (A : Table n m) (hn : 0 < n) (S : Finset (Fin m)) (j : Fin m) (N : ℕ) : ℕ :=
  ((range N).filter (fun i => 2 ≤ (candFrom A hn S j i).card)).card

theorem forksN_indep (A : Table n m) (hA : DistinctColumns A) (hn : 0 < n)
    (S : Finset (Fin m)) (j : Fin m) (hj : j ∈ S) {N N' : ℕ} (hN : S.card ≤ N)
    (hN' : S.card ≤ N') : forksN A hn S j N = forksN A hn S j N' := by
  unfold forksN
  congr 1
  ext i
  simp only [mem_filter, mem_range]
  constructor
  · rintro ⟨-, h⟩
    have := candFrom_fork_bound A hA hn S j hj i h
    exact ⟨by omega, h⟩
  · rintro ⟨-, h⟩
    have := candFrom_fork_bound A hA hn S j hj i h
    exact ⟨by omega, h⟩

theorem forksN_succ (A : Table n m) (hn : 0 < n) (S : Finset (Fin m)) (j : Fin m) (N : ℕ)
    (hS : 2 ≤ S.card) :
    forksN A hn S j (N + 1) = forksN A hn (candidateStep A S j hn) j N + 1 := by
  unfold forksN
  rw [Finset.card_filter, Finset.card_filter, Finset.sum_range_succ']
  simp only [candFrom_succ', candFrom_zero]
  congr 1
  simp [hS]

/-- The total depth `∑_{j ∈ S} (forks on the path of j below S)`. -/
def totalDepth (A : Table n m) (hn : 0 < n) (S : Finset (Fin m)) : ℕ :=
  ∑ j ∈ S, forksN A hn S j S.card

theorem totalDepth_le_one (A : Table n m) (hn : 0 < n) (S : Finset (Fin m))
    (hS : S.card ≤ 1) : totalDepth A hn S = 0 := by
  unfold totalDepth
  apply Finset.sum_eq_zero
  intro j _
  unfold forksN
  rw [Finset.card_eq_zero, Finset.filter_eq_empty_iff]
  intro i hi
  simp only [mem_range] at hi
  have : i = 0 := by omega
  subst this
  simp [candFrom_zero]; omega

/-- The child of `S` on the side `b` of the greedy row. -/
def child (A : Table n m) (hn : 0 < n) (S : Finset (Fin m)) (b : Bool) : Finset (Fin m) :=
  S.filter (fun k => A (greedyRow A S hn) k = b)

theorem candidateStep_eq_child (A : Table n m) (hn : 0 < n) (S : Finset (Fin m)) (j : Fin m)
    (hS : 2 ≤ S.card) : candidateStep A S j hn = child A hn S (A (greedyRow A S hn) j) := by
  unfold candidateStep child
  rw [if_neg (by omega)]

theorem child_card_add (A : Table n m) (hn : 0 < n) (S : Finset (Fin m)) :
    (child A hn S true).card + (child A hn S false).card = S.card := by
  unfold child
  have := Finset.card_filter_add_card_filter_not
    (s := S) (fun k => A (greedyRow A S hn) k = true)
  simpa using this

theorem child_card_lt (A : Table n m) (hA : DistinctColumns A) (hn : 0 < n)
    (S : Finset (Fin m)) (hS : 2 ≤ S.card) (b : Bool) : (child A hn S b).card < S.card := by
  obtain ⟨j, hj⟩ : S.Nonempty := Finset.card_pos.mp (by omega)
  have hq := p1_greedy_quality_pos A hA S j hn hj hS
  have hpos : 0 < (child A hn S (!b)).card := by
    have h1 : 0 < ones A S (greedyRow A S hn) := (lt_min_iff.mp hq).1
    have h0 : 0 < zeros A S (greedyRow A S hn) := (lt_min_iff.mp hq).2
    cases b
    · simpa [child, ones] using h1
    · simpa [child, zeros] using h0
  have hadd := child_card_add A hn S
  cases b
  · change 0 < (child A hn S true).card at hpos
    omega
  · change 0 < (child A hn S false).card at hpos
    omega

/-- The recursion of a binary tree: `D(S) = |S| + D(S_1) + D(S_0)` at a fork. -/
theorem totalDepth_fork (A : Table n m) (hA : DistinctColumns A) (hn : 0 < n)
    (S : Finset (Fin m)) (hS : 2 ≤ S.card) :
    totalDepth A hn S =
      S.card + totalDepth A hn (child A hn S true) + totalDepth A hn (child A hn S false) := by
  have hstep : ∀ j ∈ S, forksN A hn S j S.card =
      forksN A hn (child A hn S (A (greedyRow A S hn) j)) j
        (child A hn S (A (greedyRow A S hn) j)).card + 1 := by
    intro j hj
    obtain ⟨N, hN⟩ : ∃ N, S.card = N + 1 := ⟨S.card - 1, by omega⟩
    rw [hN, forksN_succ A hn S j N hS, candidateStep_eq_child A hn S j hS]
    congr 1
    have hjc : j ∈ child A hn S (A (greedyRow A S hn) j) := by simp [child, hj]
    have hlt := child_card_lt A hA hn S hS (A (greedyRow A S hn) j)
    exact forksN_indep A hA hn _ j hjc (by omega) le_rfl
  unfold totalDepth
  rw [Finset.sum_congr rfl hstep, Finset.sum_add_distrib, Finset.sum_const, smul_eq_mul, mul_one]
  rw [← Finset.sum_filter_add_sum_filter_not S (fun j => A (greedyRow A S hn) j = true)]
  have ht : ∀ j ∈ S.filter (fun j => A (greedyRow A S hn) j = true),
      forksN A hn (child A hn S (A (greedyRow A S hn) j)) j
        (child A hn S (A (greedyRow A S hn) j)).card =
      forksN A hn (child A hn S true) j (child A hn S true).card := by
    intro j hj; rw [(Finset.mem_filter.mp hj).2]
  have hf : ∀ j ∈ S.filter (fun j => ¬A (greedyRow A S hn) j = true),
      forksN A hn (child A hn S (A (greedyRow A S hn) j)) j
        (child A hn S (A (greedyRow A S hn) j)).card =
      forksN A hn (child A hn S false) j (child A hn S false).card := by
    intro j hj; simp only [Bool.not_eq_true, Finset.mem_filter] at hj; rw [hj.2]
  rw [Finset.sum_congr rfl ht, Finset.sum_congr rfl hf]
  have e1 : S.filter (fun j => A (greedyRow A S hn) j = true) = child A hn S true := rfl
  have e2 : S.filter (fun j => ¬A (greedyRow A S hn) j = true) = child A hn S false := by
    unfold child; congr 1; ext k; simp
  rw [e1, e2]
  ring

/-- `L_j` is the number of forks below the root, and `∑_j L_j` is the total depth of `univ`. -/
theorem leafDepth_eq_forksN (A : Table n m) (hA : DistinctColumns A) (hn : 0 < n) (j : Fin m) :
    leafDepth A hn j = forksN A hn univ j m := by
  unfold leafDepth forksN
  have hset : {i : ℕ | 2 ≤ (candidateAt A j hn i).card} =
      ↑((range m).filter (fun i => 2 ≤ (candFrom A hn univ j i).card)) := by
    ext i
    simp only [Set.mem_setOf_eq, coe_filter, mem_range, candidateAt_eq_candFrom]
    constructor
    · intro h
      have := candFrom_fork_bound A hA hn univ j (mem_univ j) i h
      simp only [card_univ, Fintype.card_fin] at this
      exact ⟨by omega, h⟩
    · exact fun h => h.2
  rw [hset, Set.ncard_coe_finset]

theorem sum_leafDepth_eq_totalDepth (A : Table n m) (hA : DistinctColumns A) (hn : 0 < n) :
    ∑ j : Fin m, leafDepth A hn j = totalDepth A hn univ := by
  unfold totalDepth
  simp only [card_univ, Fintype.card_fin]
  exact Finset.sum_congr rfl (fun j _ => leafDepth_eq_forksN A hA hn j)

end GradientKey.Concrete
