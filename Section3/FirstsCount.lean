import StirlingSum
import RowList

/-!
# Counting sequences by their distinct entries in order of first appearance

For a finite type `T`, a sequence `τ : Fin n → T` with `k` distinct entries in a given order of first
appearance can be chosen in `S(n,k)` ways. So for every `Φ : List T → ℤ`,
`∑_τ Φ(firsts τ) = ∑_k S(n,k) ∑_{e : Fin k ↪ T} Φ(e)`.
-/

namespace GradientKey.Concrete

open Finset

variable {T : Type*} [Fintype T] [DecidableEq T]

/-- `∑_{e : Fin k ↪ T} Φ(e_0, …, e_{k-1})`. -/
noncomputable def embSum (Φ : List T → ℤ) (k : ℕ) : ℤ := ∑ e : Fin k ↪ T, Φ (List.ofFn e)

theorem ofFn_snoc {n : ℕ} (τ : Fin n → T) (a : T) :
    List.ofFn (Fin.snoc τ a : Fin (n + 1) → T) = List.ofFn τ ++ [a] := by
  rw [List.ofFn_succ', List.concat_eq_append]
  simp

theorem sum_snoc {n : ℕ} (g : (Fin (n + 1) → T) → ℤ) :
    ∑ τ, g τ = ∑ τ' : Fin n → T, ∑ a : T, g (Fin.snoc τ' a) := by
  rw [← (Fin.snocEquiv (fun _ => T)).sum_comp, Fintype.sum_prod_type, Finset.sum_comm]
  rfl

theorem snoc_injective {k : ℕ} (e : Fin k ↪ T) (a : T) (ha : a ∉ Set.range e) :
    Function.Injective (Fin.snoc e a : Fin (k + 1) → T) := by
  intro x y h
  induction x using Fin.lastCases with
  | last =>
    induction y using Fin.lastCases with
    | last => rfl
    | cast y => simp at h; exact absurd ⟨y, h.symm⟩ ha
  | cast x =>
    induction y using Fin.lastCases with
    | last => simp at h; exact absurd ⟨x, h⟩ ha
    | cast y => simp only [Fin.snoc_castSucc] at h; rw [e.injective h]

/-- `(e, a)` with `a ∉ range e` corresponds to an embedding of `Fin (k+1)`. -/
def snocEmbEquiv (k : ℕ) : {p : (Fin k ↪ T) × T // p.2 ∉ Set.range p.1} ≃ (Fin (k + 1) ↪ T) where
  toFun p := ⟨Fin.snoc p.1.1 p.1.2, snoc_injective p.1.1 p.1.2 p.2⟩
  invFun e' := ⟨(⟨fun i => e' (Fin.castSucc i), fun i j h => Fin.castSucc_injective _ (e'.injective h)⟩,
      e' (Fin.last k)), by
    rintro ⟨i, hi⟩
    exact absurd (e'.injective hi) (Fin.castSucc_ne_last i)⟩
  left_inv p := by
    obtain ⟨⟨e, a⟩, h⟩ := p
    simp only [Function.Embedding.coeFn_mk, Fin.snoc_castSucc, Fin.snoc_last]
    rfl
  right_inv e' := by
    ext i
    induction i using Fin.lastCases with
    | last => simp
    | cast i => simp; rfl

theorem embSum_succ (Φ : List T → ℤ) (k : ℕ) :
    ∑ e : Fin k ↪ T, ∑ a : T, (if a ∈ Set.range e then 0 else Φ (List.ofFn e ++ [a])) =
      embSum Φ (k + 1) := by
  classical
  unfold embSum
  rw [← (snocEmbEquiv (T := T) k).sum_comp]
  have h := Finset.sum_subtype (p := fun q : (Fin k ↪ T) × T => q.2 ∉ Set.range q.1) (F := inferInstance)
    (univ.filter (fun p : (Fin k ↪ T) × T => p.2 ∉ Set.range p.1))
    (fun p => by simp) (fun p => Φ (List.ofFn (Fin.snoc p.1 p.2 : Fin (k + 1) → T)))
  change _ = ∑ p : {q : (Fin k ↪ T) × T // q.2 ∉ Set.range q.1}, Φ (List.ofFn (Fin.snoc p.1.1 p.1.2 : Fin (k + 1) → T))
  rw [← h, Finset.sum_filter, ← Finset.univ_product_univ, Finset.sum_product]
  apply sum_congr rfl; intro e _; apply sum_congr rfl; intro a _
  dsimp only
  by_cases h1 : a ∈ Set.range e
  · rw [if_pos h1, if_neg (not_not.mpr h1)]
  · rw [if_neg h1, if_pos h1, ofFn_snoc]

theorem card_mem_ofFn {k : ℕ} (e : Fin k ↪ T) :
    (univ.filter (fun a : T => a ∈ Set.range e)).card = k := by
  have : univ.filter (fun a : T => a ∈ Set.range e) = univ.map e := by
    ext a; simp
  rw [this, card_map, card_univ, Fintype.card_fin]

/-- The counting identity, for every `n ≥ 0`. -/
theorem sum_firsts (n : ℕ) (Φ : List T → ℤ) :
    ∑ τ : Fin n → T, Φ (firsts (List.ofFn τ)) =
      ∑ k ∈ range (n + 1), (Nat.stirlingSecond n k : ℤ) * embSum Φ k := by
  induction n generalizing Φ with
  | zero =>
    simp only [List.ofFn_zero, firsts_nil, Finset.sum_const, card_univ, zero_add, range_one,
      sum_singleton, Nat.stirlingSecond_zero, Nat.cast_one, one_mul, embSum]
    simp
  | succ n ih =>
    set Φ1 : List T → ℤ := fun t => ∑ a : T, (if a ∈ t then Φ t else Φ (t ++ [a])) with hΦ1
    have hstep : ∑ τ : Fin (n + 1) → T, Φ (firsts (List.ofFn τ)) =
        ∑ τ' : Fin n → T, Φ1 (firsts (List.ofFn τ')) := by
      rw [sum_snoc]
      apply sum_congr rfl; intro τ' _
      apply sum_congr rfl; intro a _
      rw [ofFn_snoc, firsts_concat]
      split_ifs <;> rfl
    rw [hstep, ih Φ1]
    have hE : ∀ k, embSum Φ1 k = k * embSum Φ k + embSum Φ (k + 1) := by
      intro k
      rw [← embSum_succ]
      unfold embSum
      rw [mul_sum, ← sum_add_distrib]
      apply sum_congr rfl; intro e _
      simp only [hΦ1, List.mem_ofFn']
      have hsplit : ∀ a : T, (if a ∈ Set.range e then Φ (List.ofFn e) else Φ (List.ofFn e ++ [a])) =
          (if a ∈ Set.range e then Φ (List.ofFn e) else 0) +
            (if a ∈ Set.range e then 0 else Φ (List.ofFn e ++ [a])) := by
        intro a; split_ifs <;> simp
      rw [sum_congr rfl (fun a _ => hsplit a), sum_add_distrib, ← sum_filter, sum_const,
        card_mem_ofFn, nsmul_eq_mul]
    simp only [hE]
    -- reindex with `S(n+1,k+1) = (k+1) S(n,k+1) + S(n,k)`
    rw [sum_range_succ' _ (n + 1)]
    simp only [Nat.stirlingSecond_succ_zero, Nat.cast_zero, zero_mul, add_zero,
      Nat.stirlingSecond_succ_succ]
    have hsplit2 : ∑ k ∈ range (n + 1), (Nat.stirlingSecond n k : ℤ) * (k * embSum Φ k + embSum Φ (k + 1)) =
        ∑ k ∈ range (n + 1), (Nat.stirlingSecond n k : ℤ) * (k * embSum Φ k) +
          ∑ k ∈ range (n + 1), (Nat.stirlingSecond n k : ℤ) * embSum Φ (k + 1) := by
      rw [← sum_add_distrib]; apply sum_congr rfl; intro k _; ring
    have h1 : ∑ k ∈ range (n + 1), (Nat.stirlingSecond n k : ℤ) * (k * embSum Φ k) =
        ∑ k ∈ range (n + 1), ((k : ℤ) + 1) * (Nat.stirlingSecond n (k + 1) : ℤ) * embSum Φ (k + 1) := by
      rw [sum_range_succ', sum_range_succ]
      simp only [Nat.cast_zero, zero_mul, mul_zero, add_zero,
        Nat.stirlingSecond_eq_zero_of_lt (show n < n + 1 by omega), Nat.cast_zero]
      apply sum_congr rfl; intro k _; push_cast; ring
    rw [hsplit2, h1, ← sum_add_distrib]
    apply sum_congr rfl; intro k _; push_cast; ring

end GradientKey.Concrete
