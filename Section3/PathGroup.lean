import PathRowCount
import PathDefs

/-!
# Proposition 3.1: grouping the set partitions of the cells by type

The set partitions `ps j` of the cells enter the path count only through the product of their Möbius
weights and through their types (`rowcount_eq_cntU`). Grouping the sum over `ps` by the types gives the
sum over integer partitions `λ_j : PathPartition m a_j` with the coefficients `∏_j c(λ_j)`
(`sum_mu_pi`).
-/

noncomputable section

namespace GradientKey.Concrete

open Finset Classical

variable {n m d : ℕ}

/-- Grouping a sum over a product of finite types by a map on each factor. -/
theorem sum_pi_fiber {ι : Type*} [Fintype ι] [DecidableEq ι] {X Y : ι → Type*}
    [∀ i, Fintype (X i)] [∀ i, Fintype (Y i)] (ψ : ∀ i, X i → Y i) (w : ∀ i, X i → ℚ)
    (H : (∀ i, Y i) → ℚ) :
    ∑ x : (∀ i, X i), (∏ i, w i (x i)) * H (fun i => ψ i (x i)) =
      ∑ y : (∀ i, Y i), (∏ i, ∑ c ∈ univ.filter (fun c => ψ i c = y i), w i c) * H y := by
  rw [← Finset.sum_fiberwise univ (fun x i => ψ i (x i))]
  apply sum_congr rfl
  intro y _
  have hfil : (univ.filter (fun x : (∀ i, X i) => (fun i => ψ i (x i)) = y)) =
      Fintype.piFinset (fun i => univ.filter (fun c => ψ i c = y i)) := by
    ext x
    simp [Fintype.mem_piFinset, funext_iff]
  rw [show (∑ x ∈ univ.filter (fun x : (∀ i, X i) => (fun i => ψ i (x i)) = y),
      (∏ i, w i (x i)) * H (fun i => ψ i (x i))) =
      ∑ x ∈ univ.filter (fun x : (∀ i, X i) => (fun i => ψ i (x i)) = y), (∏ i, w i (x i)) * H y from
    sum_congr rfl (fun x hx => by rw [(mem_filter.mp hx).2])]
  rw [← sum_mul, hfil, prod_univ_sum]

/-- An integer partition as a function `ℕ → ℕ` (multiplicity of each part size). -/
def ppFun {m a : ℕ} (p : PathPartition m a) : ℕ → ℕ :=
  fun v => if h : v < m + 1 then (p.1 ⟨v, h⟩).val else 0

theorem ppFun_fin {m a : ℕ} (p : PathPartition m a) (v : Fin (m + 1)) : ppFun p v.val = (p.1 v).val := by
  simp [ppFun, v.isLt]

theorem ppFun_injective {m a : ℕ} : Function.Injective (ppFun (m := m) (a := a)) := by
  intro p p' h
  apply Subtype.ext
  funext v
  apply Fin.ext
  rw [← ppFun_fin, ← ppFun_fin, h]

theorem wt_ppFun {m a : ℕ} (p : PathPartition m a) : wt (m + 1) (ppFun p) = a := by
  unfold wt
  rw [← Fin.sum_univ_eq_sum_range (fun v => v * ppFun p v)]
  refine Eq.trans ?_ p.2.2
  apply sum_congr rfl
  intro v _
  rw [ppFun_fin]

theorem ppFun_isTy {m a : ℕ} (p : PathPartition m a) : IsTy (m + 1) a (ppFun p) := by
  refine ⟨?_, ?_, wt_ppFun p⟩
  · have := ppFun_fin p 0
    simp only [Fin.val_zero] at this
    rw [this]
    exact p.2.1
  · intro v hv
    simp [ppFun, show ¬ v < m + 1 by omega]

theorem coefB_ppFun {m a : ℕ} (p : PathPartition m a) : coefB (m + 1) a (ppFun p) = pathCoeff p := by
  unfold coefB pathCoeff
  have hpc : pc (m + 1) (ppFun p) = pathPartCount p := by
    unfold pc pathPartCount
    rw [← Fin.sum_univ_eq_sum_range (fun v => ppFun p v)]
    apply sum_congr rfl
    intro v _
    rw [ppFun_fin]
  have hPq : Pq (m + 1) (ppFun p) =
      ∏ v : Fin (m + 1), (v.val : ℚ) ^ (p.1 v).val * (((p.1 v).val.factorial : ℕ) : ℚ) := by
    unfold Pq
    rw [← Fin.prod_univ_eq_prod_range (fun v => fw v (ppFun p v))]
    apply prod_congr rfl
    intro v _
    rw [ppFun_fin]
    rfl
  rw [hpc, hPq]

theorem typeVec_le_length {a : ℕ} (c : OrderedFinpartition a) (v : ℕ) : typeVec c v ≤ c.length := by
  unfold typeVec
  exact (card_filter_le _ _).trans (by simp)

/-- The type of a set partition of an `a`-set, as an integer partition of `b = a`. -/
theorem exists_pp {a b : ℕ} (hab : a = b) (hb : b ≤ m) (c : OrderedFinpartition a) :
    ∃ p : PathPartition m b, ppFun p = typeVec c := by
  subst hab
  have hlen : c.length ≤ a := c.length_le
  have hTy := typeVec_isTy (B := m + 1) c (by omega)
  refine ⟨⟨fun v => ⟨typeVec c v.val, by have := typeVec_le_length c v.val; omega⟩, ?_, ?_⟩, ?_⟩
  · exact hTy.1
  · refine Eq.trans ?_ hTy.2.2
    unfold wt
    rw [← Fin.sum_univ_eq_sum_range (fun v => v * typeVec c v)]
  · funext v
    unfold ppFun
    split_ifs with h
    · rfl
    · exact (hTy.2.1 v (by omega)).symm

/-- The sum of `μ` over the set partitions of one cell whose type is `p` is `c(p)`. -/
theorem sum_mu_fiber {a b : ℕ} (hab : a = b) (hb : b ≤ m) (ψ : OrderedFinpartition a → PathPartition m b)
    (hψ : ∀ c, ppFun (ψ c) = typeVec c) (p : PathPartition m b) :
    ∑ c ∈ univ.filter (fun c => ψ c = p), (mu c : ℚ) = pathCoeff p := by
  have hfil : univ.filter (fun c => ψ c = p) = univ.filter (fun c => typeVec c = ppFun p) := by
    apply filter_congr
    intro c _
    rw [← hψ c]
    exact ⟨fun h => by rw [h], fun h => ppFun_injective h⟩
  rw [hfil, sum_filter]
  change tsum a (ppFun p) = _
  rw [tsum_eq_coef a (m + 1) (by omega) _ (by subst hab; exact ppFun_isTy p)]
  subst hab
  exact coefB_ppFun p

/-- **Grouping by types.** The sum over set partitions `ps j` of the cells (of sizes `a j`) of
`∏_j μ(ps j)` times a function of the types equals the sum over integer partitions `λ_j` of `b j = a j`
of `∏_j c(λ_j)` times the same function. -/
theorem sum_mu_pi (a b : Fin (d + 1) → ℕ) (hab : ∀ j, a j = b j) (hb : ∀ j, b j ≤ m)
    (K : (Fin (d + 1) → Fin (m + 1) → ℕ) → ℚ) :
    ∑ ps : (∀ j, OrderedFinpartition (a j)),
        ((∏ j, mu (ps j) : ℤ) : ℚ) * K (fun j v => typeVec (ps j) v.val) =
      ∑ parts : (∀ j, PathPartition m (b j)),
        (∏ j, pathCoeff (parts j)) * K (fun j v => ((parts j).1 v).val) := by
  choose ψ hψ using fun j (c : OrderedFinpartition (a j)) => exists_pp (hab j) (hb j) c
  have hK : ∀ ps : (∀ j, OrderedFinpartition (a j)),
      ((∏ j, mu (ps j) : ℤ) : ℚ) * K (fun j v => typeVec (ps j) v.val) =
        (∏ j, (mu (ps j) : ℚ)) * (fun y : (∀ j, PathPartition m (b j)) =>
          K (fun j v => ((y j).1 v).val)) (fun j => ψ j (ps j)) := by
    intro ps
    push_cast
    congr 2
    funext j v
    rw [← hψ j (ps j), ppFun_fin]
  rw [sum_congr rfl (fun ps _ => hK ps)]
  refine (sum_pi_fiber ψ (fun j c => (mu c : ℚ))
    (fun y : (∀ j, PathPartition m (b j)) => K (fun j v => ((y j).1 v).val))).trans ?_
  apply sum_congr rfl
  intro y _
  congr 1
  apply prod_congr rfl
  intro j _
  convert sum_mu_fiber (hab j) (hb j) (ψ j) (hψ j) (y j)

end GradientKey.Concrete
