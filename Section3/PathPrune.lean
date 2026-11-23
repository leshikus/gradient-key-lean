import PathFormula

/-!
# Proposition 3.2: the pruning claim

If a valid table has a fork at depth `d` on the path of column `j₀`, with candidate sets of sizes
`s₀,…,s_d`, then for every `j < d` (`path_shape_bounds`):

* `s_j - 1 ≤ (n - j) q_j`: at most `n - j` rows are non-constant on `S_j` (the rows tested above are
  constant there); each has a side of at most `q_j` columns, and at most one column lies in none of these
  sides, as two such columns agree on every row (`card_le_one_add_sum_rq`);
* `Δ_j ≤ 2^{n-j-1}` and `s_{j+1} ≤ 2^{n-j-1}`: the rows `ρ(0),…,ρ(j)` are constant on each of
  `S_j \ S_{j+1}` and `S_{j+1}`, so the columns of each are distinct on the other `n - j - 1` rows
  (`card_le_two_pow_of_agree`).

With the per-chain identity `chain_count`, a chain violating one of these inequalities contributes `0`
(`prop_path_prune`).
-/

noncomputable section

namespace GradientKey.Concrete

open Finset Classical

variable {n m : ℕ}

/-- A row constant on `T` has quality `0` on `T`. -/
theorem rq_const (T : Finset (Fin m)) (row : Row m) (c : Bool) (h : ∀ x ∈ T, row x = c) :
    rq T row = 0 := by
  unfold rq
  cases c
  · have : T.filter (fun k => row k = true) = ∅ := by
      rw [filter_eq_empty_iff]
      intro x hx hx'
      rw [h x hx] at hx'
      exact Bool.false_ne_true hx'
    rw [this]; simp
  · have : T.filter (fun k => row k = false) = ∅ := by
      rw [filter_eq_empty_iff]
      intro x hx hx'
      rw [h x hx] at hx'
      exact Bool.false_ne_true hx'.symm
    rw [this]; simp

/-- **Sides.** On a table with distinct columns, `|T| ≤ 1 + ∑_r (quality of row r on T)`. -/
theorem card_le_one_add_sum_rq (A : Table n m) (hA : DistinctColumns A) (T : Finset (Fin m)) :
    T.card ≤ 1 + ∑ r, rq T (A r) := by
  let b : Fin n → Bool := fun r =>
    decide ((T.filter (fun k => A r k = true)).card ≤ (T.filter (fun k => A r k = false)).card)
  have hside : ∀ r, (T.filter (fun k => A r k = b r)).card = rq T (A r) := by
    intro r
    unfold rq
    by_cases h : (T.filter (fun k => A r k = true)).card ≤ (T.filter (fun k => A r k = false)).card
    · have hb : b r = true := by simp [b, h]
      rw [hb, min_eq_left h]
    · have hb : b r = false := by simp [b, h]
      rw [hb, min_eq_right (by omega)]
  let U := T.filter (fun k => ∀ r, A r k ≠ b r)
  have hU : U.card ≤ 1 := by
    rw [card_le_one]
    intro x hx y hy
    simp only [U, mem_filter] at hx hy
    apply hA
    funext r
    show A r x = A r y
    rw [Bool.eq_not_iff.mpr (hx.2 r), Bool.eq_not_iff.mpr (hy.2 r)]
  have hsub : T ⊆ U ∪ univ.biUnion (fun r => T.filter (fun k => A r k = b r)) := by
    intro x hx
    by_cases h : ∀ r, A r x ≠ b r
    · exact mem_union_left _ (mem_filter.mpr ⟨hx, h⟩)
    · push Not at h
      obtain ⟨r, hr⟩ := h
      exact mem_union_right _ (mem_biUnion.mpr ⟨r, mem_univ _, mem_filter.mpr ⟨hx, hr⟩⟩)
  calc T.card ≤ (U ∪ univ.biUnion (fun r => T.filter (fun k => A r k = b r))).card := card_le_card hsub
    _ ≤ U.card + (univ.biUnion (fun r => T.filter (fun k => A r k = b r))).card := card_union_le _ _
    _ ≤ 1 + ∑ r, (T.filter (fun k => A r k = b r)).card := add_le_add hU card_biUnion_le
    _ = 1 + ∑ r, rq T (A r) := by rw [sum_congr rfl (fun r _ => hside r)]

/-- **Agreement.** On a table with distinct columns, a set of columns that agree on the rows of `R` has
at most `2^{n - |R|}` columns. -/
theorem card_le_two_pow_of_agree (A : Table n m) (hA : DistinctColumns A) (X : Finset (Fin m))
    (R : Finset (Fin n)) (h : ∀ r ∈ R, ∀ x ∈ X, ∀ y ∈ X, A r x = A r y) :
    X.card ≤ 2 ^ (n - R.card) := by
  have hcard : Fintype.card ({r // r ∉ R} → Bool) = 2 ^ (n - R.card) := by
    rw [Fintype.card_fun, Fintype.card_bool, Fintype.card_subtype_compl, Fintype.card_coe,
      Fintype.card_fin]
  rw [← hcard, ← card_univ]
  refine card_le_card_of_injOn (fun x (r : {r // r ∉ R}) => A r.1 x) (fun _ _ => mem_coe.mpr (mem_univ _))
    ?_
  intro x hx y hy hxy
  apply hA
  funext r
  by_cases hr : r ∈ R
  · exact h r hr x hx y hy
  · exact congrFun hxy ⟨r, hr⟩

/-- **The shape of a path that occurs.** -/
theorem path_shape_bounds (hn : 0 < n) (s : PathChain n m) (j₀ : Fin m) (A : ValidTable n m)
    (hA : MatchesChain A hn j₀ s) (j : Fin (pathChainDepth s)) :
    (pathChainSizes s j.castSucc).val - 1 ≤ (n - j.val) * pathQuality s j ∧
      pathCellSize s j.castSucc ≤ 2 ^ (n - j.val - 1) ∧
      (pathChainSizes s j.succ).val ≤ 2 ^ (n - j.val - 1) := by
  set S : Fin (pathChainDepth s + 1) → Finset (Fin m) := fun i => candidateAt A.1 j₀ hn i with hSdef
  have hfam : S ∈ pathFams s j₀ := candidates_mem_pathFams A hn j₀ s hA
  have hsz : ∀ i, (S i).card = (pathChainSizes s i).val := hA
  have h2 : ∀ k : Fin (pathChainDepth s), 2 ≤ (S k.castSucc).card := fun k => by
    rw [hsz]; exact chain_two_le s _
  obtain ⟨rho, -, hrw⟩ := rowwise_of_candidateAt A.1 A.2 hn S j₀ h2 (fun i => rfl)
  have hsplit : ∀ i : Fin (pathChainDepth s),
      S i.succ = (S i.castSucc).filter (fun k => A.1 (rho i) k = A.1 (rho i) j₀) :=
    fun i => ((hrw (rho i)) i).1 rfl
  -- the row `ρ(i)` takes the value of `j₀` on `S_l` for `l > i`
  have hconst : ∀ (i : Fin (pathChainDepth s)) (l : Fin (pathChainDepth s + 1)), i.val < l.val →
      ∀ x ∈ S l, A.1 (rho i) x = A.1 (rho i) j₀ := by
    intro i l hil x hx
    have hx' : x ∈ S i.succ := subset_of_rowwise hrw (k := i.succ) (l := l) (by simp; omega) hx
    rw [hsplit i, mem_filter] at hx'
    exact hx'.2
  have hR : ∀ (i : Fin (pathChainDepth s)), (Finset.Iic i).card = i.val + 1 := fun i => Fin.card_Iic i
  have hn1 : j.val < n := by
    have := s.1.1.isLt
    have := j.isLt
    unfold pathChainDepth at *
    omega
  refine ⟨?_, ?_, ?_⟩
  · -- `s_j ≤ 1 + (n - j) q_j`
    have hq : ∀ r, rq (S j.castSucc) (A.1 r) ≤ fixedPathQuality S j := by
      intro r
      by_cases hr : rho j = r
      · subst hr
        rw [← quality_eq_rq, quality_selected A.1 S j₀ j (rho j) (hsplit j)]
      · have := ((hrw r) j).2 hr
        split_ifs at this <;> omega
    let Rj := (Finset.Iio j).map rho
    have hRj : Rj.card = j.val := by simp [Rj]
    have hzero : ∑ r ∈ Rj, rq (S j.castSucc) (A.1 r) = 0 := by
      apply sum_eq_zero
      intro r hr
      obtain ⟨i, hi, rfl⟩ := mem_map.mp hr
      have hi' : i.val < j.val := Fin.lt_def.mp (Finset.mem_Iio.mp hi)
      exact rq_const _ _ (A.1 (rho i) j₀) (fun x hx => hconst i j.castSucc (by simp; omega) x hx)
    have hsum : ∑ r, rq (S j.castSucc) (A.1 r) ≤ (n - j.val) * fixedPathQuality S j := by
      rw [← sum_sdiff (subset_univ Rj), hzero, add_zero]
      calc ∑ r ∈ univ \ Rj, rq (S j.castSucc) (A.1 r)
          ≤ ∑ _r ∈ univ \ Rj, fixedPathQuality S j := sum_le_sum (fun r _ => hq r)
        _ = (n - j.val) * fixedPathQuality S j := by
          rw [sum_const, card_sdiff_of_subset (subset_univ Rj), card_univ, Fintype.card_fin, hRj,
            smul_eq_mul]
    have hT := card_le_one_add_sum_rq A.1 A.2 (S j.castSucc)
    rw [fam_quality hfam j] at hsum
    rw [hsz] at hT
    omega
  · -- `Δ_j ≤ 2^{n-j-1}`
    have hsub : S j.succ ⊆ S j.castSucc :=
      subset_of_rowwise hrw (k := j.castSucc) (l := j.succ) (by simp)
    have hcell : (S j.castSucc \ S j.succ).card = pathCellSize s j.castSucc := by
      rw [card_sdiff_of_subset hsub, hsz, hsz, pathCellSize_castSucc]
    rw [← hcell]
    have := card_le_two_pow_of_agree A.1 A.2 (S j.castSucc \ S j.succ) ((Finset.Iic j).map rho) ?_
    · rw [card_map, hR] at this
      rwa [show n - (j.val + 1) = n - j.val - 1 by omega] at this
    intro r hr x hx y hy
    obtain ⟨i, hi, rfl⟩ := mem_map.mp hr
    have hi' : i.val ≤ j.val := Fin.le_def.mp (Finset.mem_Iic.mp hi)
    rw [mem_sdiff] at hx hy
    rcases hi'.lt_or_eq with hlt | heq
    · rw [hconst i j.castSucc (by simp; omega) x hx.1, hconst i j.castSucc (by simp; omega) y hy.1]
    · have he : i = j := Fin.ext heq
      subst he
      have hx2 : A.1 (rho i) x ≠ A.1 (rho i) j₀ := fun h => hx.2 (by rw [hsplit i, mem_filter]; exact ⟨hx.1, h⟩)
      have hy2 : A.1 (rho i) y ≠ A.1 (rho i) j₀ := fun h => hy.2 (by rw [hsplit i, mem_filter]; exact ⟨hy.1, h⟩)
      revert hx2 hy2
      cases A.1 (rho i) x <;> cases A.1 (rho i) y <;> cases A.1 (rho i) j₀ <;> simp
  · -- `s_{j+1} ≤ 2^{n-j-1}`
    rw [← hsz]
    have := card_le_two_pow_of_agree A.1 A.2 (S j.succ) ((Finset.Iic j).map rho) ?_
    · rw [card_map, hR] at this
      rwa [show n - (j.val + 1) = n - j.val - 1 by omega] at this
    intro r hr x hx y hy
    obtain ⟨i, hi, rfl⟩ := mem_map.mp hr
    have hi' : i.val ≤ j.val := Fin.le_def.mp (Finset.mem_Iic.mp hi)
    rw [hconst i j.succ (by simp; omega) x hx, hconst i j.succ (by simp; omega) y hy]

/-- **Proposition 3.2, pruning.** A chain contributes `0` if for some `j < d` either
`q_j (n - j) < s_j - 1` or `max(Δ_j, s_{j+1}) > 2^{n-j-1}`. -/
theorem prop_path_prune (s : PathChain n m) (j : Fin (pathChainDepth s))
    (h : (n - j.val) * pathQuality s j < (pathChainSizes s j.castSucc).val - 1 ∨
      2 ^ (n - j.val - 1) < max (pathCellSize s j.castSucc) (pathChainSizes s j.succ).val) :
    pathChainTerm s = 0 := by
  have hn : 0 < n := Fin.pos s.1.1
  have hm : 0 < m := by
    have h1 := chain_zero s
    have h2 := chain_two_le s 0
    omega
  rw [← chain_count hn s ⟨0, hm⟩, Nat.cast_eq_zero, card_eq_zero, filter_eq_empty_iff]
  intro A _ hA
  obtain ⟨b1, b2, b3⟩ := path_shape_bounds hn s ⟨0, hm⟩ A hA j
  rcases h with h | h
  · exact absurd h (not_lt.mpr b1)
  · rw [lt_max_iff] at h
    rcases h with h | h
    · exact absurd h (not_lt.mpr b2)
    · exact absurd h (not_lt.mpr b3)

end GradientKey.Concrete
