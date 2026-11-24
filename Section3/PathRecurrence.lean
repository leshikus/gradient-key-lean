import PathExample

/-!
# Section 3.1: the row-by-row recurrence for `F_n`

The article computes `F_n` of equation (1) row by row. For a set `M` of depths, `D_i(M)` is the sum of
`∏_{i' ≤ i, i' ∉ im ρ} W(M_{i'}) ∏_{j ∈ M} V_j(M_{ρ(j)})` over the injective maps `ρ : M → {1,…,i}`, where
`M_{i'} = {j ∈ M : ρ(j) < i'}`. Then `D_0(∅) = 1`, `D_0(M) = 0` for `M ≠ ∅`,
`D_{i+1}(M) = D_i(M) W(M) + ∑_{j ∈ M} D_i(M ∖ {j}) V_j(M ∖ {j})`, and `F_n = D_n({0,…,d-1})`.

Lean rows are `0`-based: row `i+1` of the article is `i : Fin n`.

* `pathD`: the recurrence, as a definition.
* `pathD_eq_sum`: `pathD` is the article's sum over the injective maps `M ↪ Fin i`.
* `pathF_eq_pathD`: `pathF s parts = pathD s parts n univ`.
* `example34_D`: the four values `1032, 296, 296, 56` of the chain `(4,2)` of the example `(3,4)`, computed by
  unfolding the recurrence from the values of `W` and `V_0` (`example34_W`, `example34_V`).

The proof goes through row schedules `τ : Fin i → Option (Fin d)` (row `r` tests depth `j` iff `τ r = some j`), for
generic weights `W` and `V`. This file does not verify the C++ engine.
-/

noncomputable section

namespace GradientKey.Concrete

open Finset Classical

section Generic

variable {d : ℕ} (W : Finset (Fin d) → ℕ) (V : Fin d → Finset (Fin d) → ℕ)

/-- The recurrence for generic weights. -/
def recD : ℕ → Finset (Fin d) → ℕ
  | 0, M => if M = ∅ then 1 else 0
  | i + 1, M => recD i M * W M + ∑ j ∈ M, recD i (M.erase j) * V j (M.erase j)

/-- `M_r = {j ∈ M : ρ(j) < r}` for an injective map `ρ : M → Fin i`. -/
def injBefore {M : Finset (Fin d)} {i : ℕ} (ρ : M ↪ Fin i) (r : Fin i) : Finset (Fin d) :=
  (univ.filter (fun j : M => ρ j < r)).map (Function.Embedding.subtype _)

/-- The article's `D_i(M)` for generic weights. -/
def injSum (i : ℕ) (M : Finset (Fin d)) : ℕ :=
  ∑ ρ : M ↪ Fin i,
    (∏ r ∈ univ.filter (fun r : Fin i => ∀ j : M, ρ j ≠ r), W (injBefore ρ r)) *
      ∏ j : M, V j (injBefore ρ (ρ j))

/-- A schedule tests each depth of `M` at exactly one row, and no other depth. -/
def SchedValid {i : ℕ} (M : Finset (Fin d)) (τ : Fin i → Option (Fin d)) : Prop :=
  (∀ r r' j, τ r = some j → τ r' = some j → r = r') ∧ ∀ j, j ∈ M ↔ ∃ r, τ r = some j

/-- The depths tested before row `r`. -/
def schedBefore {i : ℕ} (τ : Fin i → Option (Fin d)) (r : Fin i) : Finset (Fin d) :=
  univ.filter (fun j => ∃ r', r' < r ∧ τ r' = some j)

/-- The weight of row `r`. -/
def schedWt {i : ℕ} (τ : Fin i → Option (Fin d)) (r : Fin i) : ℕ :=
  match τ r with
  | none => W (schedBefore τ r)
  | some j => V j (schedBefore τ r)

/-- The sum over the schedules. -/
def schedSum (i : ℕ) (M : Finset (Fin d)) : ℕ :=
  ∑ τ : Fin i → Option (Fin d), if SchedValid M τ then ∏ r, schedWt W V τ r else 0

theorem schedBefore_snoc_castSucc {i : ℕ} (τ : Fin i → Option (Fin d)) (o : Option (Fin d)) (r : Fin i) :
    schedBefore (Fin.snoc τ o : Fin (i + 1) → Option (Fin d)) (Fin.castSucc r) = schedBefore τ r := by
  ext j
  simp only [schedBefore, mem_filter, mem_univ, true_and]
  constructor
  · rintro ⟨r', hr', h⟩
    have hlt : r'.val < i := lt_trans hr' r.isLt
    refine ⟨⟨r'.val, hlt⟩, hr', ?_⟩
    have : r' = Fin.castSucc ⟨r'.val, hlt⟩ := rfl
    rw [this, Fin.snoc_castSucc] at h
    exact h
  · rintro ⟨r', hr', h⟩
    exact ⟨Fin.castSucc r', Fin.castSucc_lt_castSucc_iff.mpr hr', by rw [Fin.snoc_castSucc]; exact h⟩

theorem schedBefore_snoc_last {i : ℕ} (τ : Fin i → Option (Fin d)) (o : Option (Fin d)) :
    schedBefore (Fin.snoc τ o : Fin (i + 1) → Option (Fin d)) (Fin.last i) =
      univ.filter (fun j => ∃ r, τ r = some j) := by
  ext j
  simp only [schedBefore, mem_filter, mem_univ, true_and]
  constructor
  · rintro ⟨r', hr', h⟩
    have hlt : r'.val < i := hr'
    refine ⟨⟨r'.val, hlt⟩, ?_⟩
    have : r' = Fin.castSucc ⟨r'.val, hlt⟩ := rfl
    rw [this, Fin.snoc_castSucc] at h
    exact h
  · rintro ⟨r', h⟩
    exact ⟨Fin.castSucc r', Fin.castSucc_lt_last r', by rw [Fin.snoc_castSucc]; exact h⟩

theorem image_of_valid {i : ℕ} {M : Finset (Fin d)} {τ : Fin i → Option (Fin d)} (h : SchedValid M τ) :
    univ.filter (fun j => ∃ r, τ r = some j) = M := by
  ext j; simp [h.2 j]

theorem prod_snoc {i : ℕ} (τ : Fin i → Option (Fin d)) (o : Option (Fin d)) :
    ∏ r, schedWt W V (Fin.snoc τ o : Fin (i + 1) → Option (Fin d)) r =
      (∏ r, schedWt W V τ r) *
        (match o with
          | none => W (univ.filter (fun j => ∃ r, τ r = some j))
          | some j => V j (univ.filter (fun j => ∃ r, τ r = some j))) := by
  rw [Fin.prod_univ_castSucc]
  congr 1
  · apply prod_congr rfl; intro r _
    unfold schedWt
    rw [Fin.snoc_castSucc, schedBefore_snoc_castSucc]
  · unfold schedWt
    rw [Fin.snoc_last, schedBefore_snoc_last]

theorem valid_snoc_none {i : ℕ} (M : Finset (Fin d)) (τ : Fin i → Option (Fin d)) :
    SchedValid M (Fin.snoc τ none : Fin (i + 1) → Option (Fin d)) ↔ SchedValid M τ := by
  have key : ∀ (r : Fin (i + 1)) j, (Fin.snoc τ none : Fin (i + 1) → Option (Fin d)) r = some j ↔
      ∃ r' : Fin i, r = Fin.castSucc r' ∧ τ r' = some j := by
    intro r j
    refine Fin.lastCases ?_ (fun r' => ?_) r
    · simp only [Fin.snoc_last, reduceCtorEq, false_iff, not_exists, not_and]
      intro r' h; exact absurd h.symm (Fin.castSucc_ne_last r')
    · simp only [Fin.snoc_castSucc]
      constructor
      · intro h; exact ⟨r', rfl, h⟩
      · rintro ⟨r'', h1, h2⟩; rw [Fin.castSucc_inj.mp h1]; exact h2
  constructor
  · rintro ⟨h1, h2⟩
    refine ⟨fun r r' j hr hr' => ?_, fun j => ?_⟩
    · exact Fin.castSucc_inj.mp (h1 _ _ j ((key _ j).mpr ⟨r, rfl, hr⟩) ((key _ j).mpr ⟨r', rfl, hr'⟩))
    · rw [h2 j]
      constructor
      · rintro ⟨r, hr⟩; obtain ⟨r', -, h⟩ := (key r j).mp hr; exact ⟨r', h⟩
      · rintro ⟨r, hr⟩; exact ⟨_, (key _ j).mpr ⟨r, rfl, hr⟩⟩
  · rintro ⟨h1, h2⟩
    refine ⟨fun r r' j hr hr' => ?_, fun j => ?_⟩
    · obtain ⟨a, rfl, ha⟩ := (key r j).mp hr
      obtain ⟨b, rfl, hb⟩ := (key r' j).mp hr'
      rw [h1 a b j ha hb]
    · rw [h2 j]
      constructor
      · rintro ⟨r, hr⟩; exact ⟨_, (key _ j).mpr ⟨r, rfl, hr⟩⟩
      · rintro ⟨r, hr⟩; obtain ⟨r', -, h⟩ := (key r j).mp hr; exact ⟨r', h⟩

theorem valid_snoc_some {i : ℕ} (M : Finset (Fin d)) (τ : Fin i → Option (Fin d)) (j : Fin d) :
    SchedValid M (Fin.snoc τ (some j) : Fin (i + 1) → Option (Fin d)) ↔
      j ∈ M ∧ SchedValid (M.erase j) τ := by
  set τ' : Fin (i + 1) → Option (Fin d) := Fin.snoc τ (some j) with hτ'
  have hc : ∀ r, τ' (Fin.castSucc r) = τ r := fun r => Fin.snoc_castSucc _ _ _
  have hl : τ' (Fin.last i) = some j := Fin.snoc_last _ _
  constructor
  · rintro ⟨h1, h2⟩
    have hj : j ∈ M := (h2 j).mpr ⟨_, hl⟩
    have hno : ∀ r, τ r ≠ some j := by
      intro r hr
      have := h1 _ _ j ((hc r).trans hr) hl
      exact Fin.castSucc_ne_last r this
    refine ⟨hj, fun r r' k hr hr' => ?_, fun k => ?_⟩
    · exact Fin.castSucc_inj.mp (h1 _ _ k ((hc r).trans hr) ((hc r').trans hr'))
    · rw [mem_erase, h2 k]
      constructor
      · rintro ⟨hkj, r, hr⟩
        refine Fin.lastCases (fun h => ?_) (fun r' h => ⟨r', (hc r').symm.trans h⟩) r hr
        rw [hl] at h; exact absurd (Option.some_inj.mp h).symm hkj
      · rintro ⟨r, hr⟩
        exact ⟨fun hkj => hno r (hkj ▸ hr), _, (hc r).trans hr⟩
  · rintro ⟨hj, h1, h2⟩
    have hno : ∀ r, τ r ≠ some j := fun r hr => by
      have := (h2 j).mpr ⟨r, hr⟩; simp at this
    refine ⟨fun r r' k hr hr' => ?_, fun k => ?_⟩
    · induction r using Fin.lastCases with
      | last =>
        induction r' using Fin.lastCases with
        | last => rfl
        | cast b =>
          rw [hl] at hr; rw [hc] at hr'; rw [← hr] at hr'; exact absurd hr' (hno b)
      | cast a =>
        induction r' using Fin.lastCases with
        | last =>
          rw [hl] at hr'; rw [hc] at hr; rw [← hr'] at hr; exact absurd hr (hno a)
        | cast b =>
          rw [hc] at hr hr'; rw [h1 a b k hr hr']
    · by_cases hkj : k = j
      · subst hkj; exact ⟨fun _ => ⟨_, hl⟩, fun _ => hj⟩
      · have := h2 k
        rw [mem_erase] at this
        constructor
        · intro hk
          obtain ⟨r, hr⟩ := this.mp ⟨hkj, hk⟩
          exact ⟨_, (hc r).trans hr⟩
        · rintro ⟨r, hr⟩
          induction r using Fin.lastCases with
          | last => rw [hl] at hr; exact absurd (Option.some_inj.mp hr).symm hkj
          | cast a => rw [hc] at hr; exact (this.mpr ⟨a, hr⟩).2

theorem schedSum_zero (M : Finset (Fin d)) : schedSum W V 0 M = if M = ∅ then 1 else 0 := by
  unfold schedSum
  have hv : ∀ τ : Fin 0 → Option (Fin d), SchedValid M τ ↔ M = ∅ := by
    intro τ
    constructor
    · rintro ⟨-, h⟩
      ext j; simp [h j]
    · rintro rfl
      exact ⟨fun r => r.elim0, fun j => by simp⟩
  simp only [hv]
  rw [Fintype.sum_unique]
  split_ifs <;> simp

theorem sum_snoc_option {i : ℕ} (g : (Fin (i + 1) → Option (Fin d)) → ℕ) :
    ∑ τ', g τ' = ∑ τ : Fin i → Option (Fin d), g (Fin.snoc τ none) +
      ∑ j : Fin d, ∑ τ : Fin i → Option (Fin d), g (Fin.snoc τ (some j)) := by
  rw [← (Fin.snocEquiv (fun _ => Option (Fin d))).sum_comp, Fintype.sum_prod_type, Fintype.sum_option]
  rfl

theorem schedSum_succ (i : ℕ) (M : Finset (Fin d)) :
    schedSum W V (i + 1) M = schedSum W V i M * W M +
      ∑ j ∈ M, schedSum W V i (M.erase j) * V j (M.erase j) := by
  unfold schedSum
  rw [sum_snoc_option]
  congr 1
  · rw [sum_mul]
    apply sum_congr rfl; intro τ _
    rw [prod_snoc]
    by_cases h : SchedValid M τ
    · have h' := (valid_snoc_none M τ).mpr h
      simp [h, h', image_of_valid h]
    · have h' : ¬ SchedValid M (Fin.snoc τ none : Fin (i + 1) → Option (Fin d)) :=
        fun h' => h ((valid_snoc_none M τ).mp h')
      simp [h, h']
  · have hj : ∀ j : Fin d, (∑ τ : Fin i → Option (Fin d),
        (if SchedValid M (Fin.snoc τ (some j) : Fin (i + 1) → Option (Fin d)) then
          ∏ r, schedWt W V (Fin.snoc τ (some j) : Fin (i + 1) → Option (Fin d)) r else 0)) =
        if j ∈ M then (∑ τ : Fin i → Option (Fin d),
          if SchedValid (M.erase j) τ then ∏ r, schedWt W V τ r else 0) * V j (M.erase j) else 0 := by
      intro j
      by_cases hjM : j ∈ M
      · rw [if_pos hjM, sum_mul]
        apply sum_congr rfl; intro τ _
        rw [prod_snoc]
        by_cases h : SchedValid (M.erase j) τ
        · have h' := (valid_snoc_some M τ j).mpr ⟨hjM, h⟩
          simp [h, h', image_of_valid h]
        · have h' : ¬ SchedValid M (Fin.snoc τ (some j) : Fin (i + 1) → Option (Fin d)) :=
            fun h' => h ((valid_snoc_some M τ j).mp h').2
          simp [h, h']
      · rw [if_neg hjM]
        apply sum_eq_zero; intro τ _
        have h' : ¬ SchedValid M (Fin.snoc τ (some j) : Fin (i + 1) → Option (Fin d)) :=
          fun h => hjM ((valid_snoc_some M τ j).mp h).1
        simp [h']
    rw [sum_congr rfl (fun j _ => hj j), ← sum_filter, filter_mem_eq_inter, univ_inter]

theorem recD_eq_schedSum (i : ℕ) (M : Finset (Fin d)) : recD W V i M = schedSum W V i M := by
  induction i generalizing M with
  | zero => rw [schedSum_zero]; rfl
  | succ i ih =>
    rw [schedSum_succ, ← ih]
    simp only [recD, ih]

/-- The schedule of an injective map: row `r` tests `j` iff `ρ j = r`. -/
def schedOf {M : Finset (Fin d)} {i : ℕ} (ρ : M ↪ Fin i) : Fin i → Option (Fin d) :=
  fun r => (Function.partialInv ρ r).map Subtype.val

theorem schedOf_eq_some {M : Finset (Fin d)} {i : ℕ} (ρ : M ↪ Fin i) (r : Fin i) (j : Fin d) :
    schedOf ρ r = some j ↔ ∃ hj : j ∈ M, ρ ⟨j, hj⟩ = r := by
  unfold schedOf
  rw [Option.map_eq_some_iff]
  constructor
  · rintro ⟨a, ha, rfl⟩
    exact ⟨a.2, (ρ.injective.isPartialInv a r).mp ha⟩
  · rintro ⟨hj, h⟩
    exact ⟨⟨j, hj⟩, (ρ.injective.isPartialInv _ r).mpr h, rfl⟩

theorem schedOf_eq_none {M : Finset (Fin d)} {i : ℕ} (ρ : M ↪ Fin i) (r : Fin i) (h : ∀ j : M, ρ j ≠ r) :
    schedOf ρ r = none := by
  cases hs : schedOf ρ r with
  | none => rfl
  | some j =>
    obtain ⟨hj, h'⟩ := (schedOf_eq_some ρ r j).mp hs
    exact absurd h' (h _)

theorem schedOf_valid {M : Finset (Fin d)} {i : ℕ} (ρ : M ↪ Fin i) : SchedValid M (schedOf ρ) := by
  refine ⟨fun r r' j hr hr' => ?_, fun j => ?_⟩
  · obtain ⟨hj, rfl⟩ := (schedOf_eq_some ρ r j).mp hr
    obtain ⟨hj', rfl⟩ := (schedOf_eq_some ρ r' j).mp hr'
    rfl
  · constructor
    · intro hj; exact ⟨ρ ⟨j, hj⟩, (schedOf_eq_some ρ _ j).mpr ⟨hj, rfl⟩⟩
    · rintro ⟨r, hr⟩; exact ((schedOf_eq_some ρ r j).mp hr).1

theorem schedBefore_schedOf {M : Finset (Fin d)} {i : ℕ} (ρ : M ↪ Fin i) (r : Fin i) :
    schedBefore (schedOf ρ) r = injBefore ρ r := by
  ext j
  simp only [schedBefore, injBefore, mem_filter, mem_univ, true_and, mem_map,
    Function.Embedding.coe_subtype, schedOf_eq_some]
  constructor
  · rintro ⟨r', hr', hj, rfl⟩; exact ⟨⟨j, hj⟩, hr', rfl⟩
  · rintro ⟨a, ha, rfl⟩; exact ⟨ρ a, ha, a.2, rfl⟩

theorem injSum_eq_schedSum (i : ℕ) (M : Finset (Fin d)) : injSum W V i M = schedSum W V i M := by
  unfold injSum schedSum
  rw [← sum_filter]
  refine sum_bij (fun ρ _ => schedOf ρ) (fun ρ _ => mem_filter.mpr ⟨mem_univ _, schedOf_valid ρ⟩)
    (fun ρ₁ _ ρ₂ _ h => ?_) (fun τ hτ => ?_) (fun ρ _ => ?_)
  · ext j
    have h1 : schedOf ρ₁ (ρ₁ j) = some j.1 := (schedOf_eq_some ρ₁ _ _).mpr ⟨j.2, rfl⟩
    rw [h] at h1
    obtain ⟨_, h2⟩ := (schedOf_eq_some ρ₂ _ _).mp h1
    exact congrArg Fin.val h2.symm
  · have hv := (mem_filter.mp hτ).2
    have hex : ∀ j : M, ∃ r, τ r = some j.1 := fun j => (hv.2 j).mp j.2
    let ρ : M ↪ Fin i := ⟨fun j => (hex j).choose, fun a b hab => by
      have ha := (hex a).choose_spec
      have hb := (hex b).choose_spec
      simp only at hab
      rw [hab, hb] at ha
      exact Subtype.ext (Option.some_inj.mp ha).symm⟩
    have hρ : ∀ j : M, τ (ρ j) = some j.1 := fun j => (hex j).choose_spec
    refine ⟨ρ, mem_univ _, funext fun r => ?_⟩
    cases hr : τ r with
    | none =>
      apply schedOf_eq_none
      intro j hj
      rw [← hj, hρ] at hr; exact absurd hr (by simp)
    | some j =>
      have hj : j ∈ M := (hv.2 j).mpr ⟨r, hr⟩
      refine (schedOf_eq_some ρ r j).mpr ⟨hj, ?_⟩
      exact hv.1 _ _ j (hρ ⟨j, hj⟩) hr
  · rw [← prod_filter_mul_prod_filter_not univ (fun r : Fin i => ∀ j : M, ρ j ≠ r)]
    congr 1
    · apply prod_congr rfl; intro r hr
      have hn := schedOf_eq_none ρ r (mem_filter.mp hr).2
      unfold schedWt
      rw [hn, schedBefore_schedOf]
    · have hset : univ.filter (fun r : Fin i => ¬ ∀ j : M, ρ j ≠ r) = univ.map ρ := by
        ext r; simp
      rw [hset, prod_map]
      apply prod_congr rfl; intro j _
      unfold schedWt
      rw [(schedOf_eq_some ρ _ _).mpr ⟨j.2, rfl⟩, schedBefore_schedOf]

theorem recD_eq_injSum (i : ℕ) (M : Finset (Fin d)) : recD W V i M = injSum W V i M := by
  rw [recD_eq_schedSum, injSum_eq_schedSum]

end Generic

/-! ## The recurrence for `F_n` -/

/-- `D_i(M)`, defined by the article's recurrence (row `i+1` of the article is row `i` here). -/
def pathD {n m : ℕ} (s : PathChain n m) (parts : PathPartitionTypes s) :
    ℕ → Finset (Fin (pathChainDepth s)) → ℕ
  | 0, M => if M = ∅ then 1 else 0
  | i + 1, M => pathD s parts i M * pathW s parts M +
      ∑ j ∈ M, pathD s parts i (M.erase j) * pathV s parts j (M.erase j)

theorem pathD_eq_recD {n m : ℕ} (s : PathChain n m) (parts : PathPartitionTypes s) (i : ℕ)
    (M : Finset (Fin (pathChainDepth s))) :
    pathD s parts i M = recD (pathW s parts) (pathV s parts) i M := by
  induction i generalizing M with
  | zero => rfl
  | succ i ih => simp only [pathD, recD, ih]

/-- The article's definition of `D_i(M)`: the sum over the injective maps `ρ : M → Fin i` of
`∏_{r ∉ im ρ} W(M_r) ∏_{j ∈ M} V_j(M_{ρ(j)})`, with `M_r = {j ∈ M : ρ(j) < r}`. -/
theorem pathD_eq_sum {n m : ℕ} (s : PathChain n m) (parts : PathPartitionTypes s) (i : ℕ)
    (M : Finset (Fin (pathChainDepth s))) :
    pathD s parts i M =
      ∑ ρ : M ↪ Fin i,
        (∏ r ∈ univ.filter (fun r : Fin i => ∀ j : M, ρ j ≠ r),
            pathW s parts ((univ.filter (fun j : M => ρ j < r)).map (Function.Embedding.subtype _))) *
          ∏ j : M, pathV s parts j
            ((univ.filter (fun j' : M => ρ j' < ρ j)).map (Function.Embedding.subtype _)) := by
  rw [pathD_eq_recD, recD_eq_injSum]
  rfl

/-- `F_n = D_n({0,…,d-1})`. -/
theorem pathF_eq_pathD {n m : ℕ} (s : PathChain n m) (parts : PathPartitionTypes s) :
    pathF s parts = pathD s parts n univ := by
  rw [pathD_eq_recD, recD_eq_injSum]
  unfold pathF injSum
  let e : (Fin (pathChainDepth s) ↪ Fin n) ≃ ((univ : Finset (Fin (pathChainDepth s))) ↪ Fin n) :=
    { toFun := fun ρ => ⟨fun j => ρ j.1, fun a b h => Subtype.ext (ρ.injective h)⟩
      invFun := fun ρ => ⟨fun j => ρ ⟨j, mem_univ j⟩, fun a b h => congrArg Subtype.val (ρ.injective h)⟩
      left_inv := fun ρ => rfl
      right_inv := fun ρ => rfl }
  refine Fintype.sum_equiv e _ _ (fun ρ => ?_)
  have hb : ∀ r, injBefore (e ρ) r = pathBefore s ρ r := by
    intro r; ext j
    simp only [injBefore, pathBefore, mem_map, mem_filter, mem_univ, true_and,
      Function.Embedding.coe_subtype]
    constructor
    · rintro ⟨a, ha, rfl⟩; exact ha
    · intro h; exact ⟨⟨j, mem_univ j⟩, h, rfl⟩
  congr 1
  · have hf : univ.filter (fun r : Fin n => ∀ j : (univ : Finset (Fin (pathChainDepth s))), e ρ j ≠ r) =
        univ.filter (fun r : Fin n => ∀ j, ρ j ≠ r) := by
      ext r
      simp only [mem_filter, mem_univ, true_and]
      constructor
      · intro h j; exact h ⟨j, mem_univ j⟩
      · intro h j; exact h j.1
    rw [hf]
    exact prod_congr rfl (fun r _ => by rw [hb])
  · rw [← prod_coe_sort univ (fun j => pathV s parts j (pathBefore s ρ (ρ j)))]
    apply prod_congr rfl; intro j _
    rw [hb]; rfl

/-- The empty set of depths (no tested row, e.g. `d = 0`): `D_i(∅) = W(∅)^i`. -/
theorem pathD_empty {n m : ℕ} (s : PathChain n m) (parts : PathPartitionTypes s) (i : ℕ) :
    pathD s parts i ∅ = pathW s parts ∅ ^ i := by
  induction i with
  | zero => simp [pathD]
  | succ i ih => simp [pathD, ih, pow_succ]

/-- No injective map `M → Fin i` exists if `|M| > i`: then `D_i(M) = 0`. -/
theorem pathD_eq_zero_of_lt_card {n m : ℕ} (s : PathChain n m) (parts : PathPartitionTypes s) (i : ℕ)
    (M : Finset (Fin (pathChainDepth s))) (h : i < M.card) : pathD s parts i M = 0 := by
  induction i generalizing M with
  | zero =>
    have : M ≠ ∅ := fun hM => by simp [hM] at h
    simp [pathD, this]
  | succ i ih =>
    simp only [pathD]
    rw [ih M (by omega), zero_mul, zero_add]
    apply sum_eq_zero; intro j hj
    rw [ih (M.erase j) (by rw [card_erase_of_mem hj]; omega), zero_mul]

namespace Example34

open GradientKey.Concrete

theorem univ_d0 : (univ : Finset (Fin (pathChainDepth chain42))) = {d0} := by decide

theorem pathD3_d0 (parts : PathPartitionTypes chain42) :
    pathD chain42 parts 3 {d0} =
      pathV chain42 parts d0 ∅ * pathW chain42 parts {d0} ^ 2 +
        pathW chain42 parts ∅ * pathV chain42 parts d0 ∅ * pathW chain42 parts {d0} +
          pathW chain42 parts ∅ ^ 2 * pathV chain42 parts d0 ∅ := by
  simp only [pathD, sum_singleton, erase_singleton, if_pos, sum_empty, add_zero,
    show ({d0} : Finset (Fin (pathChainDepth chain42))) ≠ ∅ from singleton_ne_empty d0, if_false]
  ring

/-- The recurrence at `i = 3` on chain `(4,2)`, from `W` and `V_0`: `1032, 296, 296, 56`. -/
theorem example34_D :
    pathD chain42 P11_11 3 univ = 1032 ∧ pathD chain42 P2_11 3 univ = 296 ∧
    pathD chain42 P11_2 3 univ = 296 ∧ pathD chain42 P2_2 3 univ = 56 := by
  obtain ⟨⟨a0, a1⟩, ⟨b0, b1⟩, ⟨c0, c1⟩, ⟨e0, e1⟩⟩ := example34_W
  obtain ⟨va, vb, vc, ve⟩ := example34_V
  simp only [univ_d0, pathD3_d0, a0, a1, b0, b1, c0, c1, e0, e1, va, vb, vc, ve]
  norm_num

/-- `F_3 = D_3({0})` on the four types of chain `(4,2)`, consistent with `example34_F`. -/
theorem example34_F_eq_D :
    pathF chain42 P11_11 = pathD chain42 P11_11 3 univ ∧ pathF chain42 P2_11 = pathD chain42 P2_11 3 univ ∧
    pathF chain42 P11_2 = pathD chain42 P11_2 3 univ ∧ pathF chain42 P2_2 = pathD chain42 P2_2 3 univ := by
  obtain ⟨h1, h2, h3, h4⟩ := example34_F
  obtain ⟨k1, k2, k3, k4⟩ := example34_D
  exact ⟨h1.trans k1.symm, h2.trans k2.symm, h3.trans k3.symm, h4.trans k4.symm⟩

end Example34

end GradientKey.Concrete
