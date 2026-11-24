import SmallItems

/-!
# Section 3.2: the `B_k` are integers

After Proposition 3.3 (`prop:small-m`) the article says: the `B_k` are integers. By column symmetry
`B_k = ∑_{T ∈ 𝒯_k} L_1(G(T)) - |𝒯_k| C(m)`. Column permutations act freely on the `2^k |𝒯_k|` tables formed by
representatives of the row types of `T ∈ 𝒯_k`, so `m!` divides `2^k |𝒯_k|`; hence the odd part of `m`, the
denominator of `C(m)`, divides `|𝒯_k|`, and `|𝒯_k| C(m)` is an integer.

Here `Bint hm k = m B_k` (`SmallM`).

* `sum_ldepth_eq`: column symmetry, `∑_{T ∈ 𝒯_k} ∑_j L_j = m ∑_{T ∈ 𝒯_k} L_0`.
* `factorial_dvd_card`: `m! ∣ 2^k |𝒯_k|` (free action of the column permutations on the representative tables).
* `Bint_dvd`: `m ∣ m B_k`; `Bk_integer`: `B_k` is an integer. No condition on `k`.
-/

noncomputable section

namespace GradientKey.Concrete

open Finset Classical

variable {m : ℕ}

/-! ## Depth of one column -/

/-- The depth of column `j` in the greedy tree of the row list `L`. -/
def cdep (L : List (Row m)) (j : Fin m) : ℕ :=
  ((range m).filter (fun i => 2 ≤ (lcand L j i).card)).card

theorem ldepth_eq_sum_cdep (L : List (Row m)) : ldepth L = ∑ j, cdep L j := rfl

theorem lcand_of_lstep {L L' : List (Row m)} (hs : ∀ T j, lstep L T j = lstep L' T j) (j : Fin m) (i : ℕ) :
    lcand L j i = lcand L' j i := by
  unfold lcand
  rw [show (fun T => lstep L T j) = (fun T => lstep L' T j) from funext (fun T => hs T j)]

theorem lstep_map_canon (hm : 0 < m) (L : List (Row m)) (T : Finset (Fin m)) (j : Fin m) :
    lstep (L.map (canon hm)) T j = lstep L T j := by
  unfold lstep
  split_ifs
  · rfl
  · rw [argmax_map]
    have : rq T ∘ canon hm = rq T := funext (rq_canon hm T)
    rw [this]
    cases List.argmax (rq T) L with
    | none => rfl
    | some r =>
      simp only [Option.map_some]
      congr 1; funext k; simp only [canon_eq_iff]

theorem cdep_map_canon (hm : 0 < m) (L : List (Row m)) (j : Fin m) :
    cdep (L.map (canon hm)) j = cdep L j := by
  unfold cdep
  simp only [lcand_of_lstep (lstep_map_canon hm L) j]

/-! ## Permuting the columns -/

/-- The row `r ∘ π`. -/
def prow (π : Equiv.Perm (Fin m)) (r : Row m) : Row m := fun k => r (π k)

theorem rq_prow (π : Equiv.Perm (Fin m)) (S : Finset (Fin m)) (r : Row m) :
    rq S (prow π r) = rq (S.map π.toEmbedding) r := by
  unfold rq prow
  rw [filter_map, filter_map, card_map, card_map]
  rfl

theorem map_symm_map (π : Equiv.Perm (Fin m)) (S : Finset (Fin m)) :
    (S.map π.toEmbedding).map π.symm.toEmbedding = S := by
  ext k; simp

theorem lstep_prow (π : Equiv.Perm (Fin m)) (L : List (Row m)) (S : Finset (Fin m)) (j : Fin m) :
    lstep (L.map (prow π)) S j = (lstep L (S.map π.toEmbedding) (π j)).map π.symm.toEmbedding := by
  unfold lstep
  rw [card_map]
  split_ifs
  · exact (map_symm_map π S).symm
  · rw [argmax_map]
    have : rq S ∘ prow π = rq (S.map π.toEmbedding) := funext (rq_prow π S)
    rw [this]
    cases List.argmax (rq (S.map π.toEmbedding)) L with
    | none => exact (map_symm_map π S).symm
    | some r =>
      simp only [Option.map_some]
      ext k
      rw [mem_filter, mem_map]
      constructor
      · rintro ⟨hk, h⟩
        refine ⟨π k, ?_, by simp⟩
        rw [mem_filter]
        exact ⟨mem_map_of_mem _ hk, h⟩
      · rintro ⟨a, ha, rfl⟩
        rw [mem_filter, mem_map] at ha
        obtain ⟨⟨b, hb, rfl⟩, h⟩ := ha
        simp only [Equiv.coe_toEmbedding, Equiv.symm_apply_apply]
        exact ⟨hb, h⟩

theorem lcand_prow (π : Equiv.Perm (Fin m)) (L : List (Row m)) (j : Fin m) (i : ℕ) :
    lcand (L.map (prow π)) j i = (lcand L (π j) i).map π.symm.toEmbedding := by
  induction i with
  | zero =>
    unfold lcand
    simp only [Function.iterate_zero, id_eq]
    exact (map_univ_equiv π.symm).symm
  | succ i ih =>
    have h1 : ∀ (L : List (Row m)) j, lcand L j (i + 1) = lstep L (lcand L j i) j := by
      intro L j; unfold lcand; rw [Function.iterate_succ_apply']
    rw [h1, h1, ih, lstep_prow]
    congr 2
    ext k; simp

theorem cdep_prow (π : Equiv.Perm (Fin m)) (L : List (Row m)) (j : Fin m) :
    cdep (L.map (prow π)) j = cdep L (π j) := by
  unfold cdep
  simp only [lcand_prow, card_map]

theorem sep_prow (π : Equiv.Perm (Fin m)) (L : List (Row m)) : Sep (L.map (prow π)) ↔ Sep L := by
  unfold Sep
  simp only [List.mem_map, exists_exists_and_eq_and, prow]
  constructor
  · intro h j k hjk
    have := h (π.symm j) (π.symm k) (fun e => hjk (π.symm.injective e))
    simpa using this
  · intro h j k hjk
    exact h (π j) (π k) (fun e => hjk (π.injective e))

theorem prow_inv_prow (π : Equiv.Perm (Fin m)) (r : Row m) : prow π⁻¹ (prow π r) = r := by
  funext k; simp [prow]

theorem canon_not (hm : 0 < m) (r : Row m) : canon hm (fun k => !r k) = canon hm r := by
  unfold canon
  cases h : r ⟨0, hm⟩ <;> simp [h]

theorem canon_prow_canon (hm : 0 < m) (π : Equiv.Perm (Fin m)) (r : Row m) :
    canon hm (prow π (canon hm r)) = canon hm (prow π r) := by
  by_cases h : r ⟨0, hm⟩ = true
  · have : canon hm r = fun k => !r k := by unfold canon; rw [if_pos h]
    rw [this, ← canon_not hm (prow π r)]
    rfl
  · have : canon hm r = r := by unfold canon; rw [if_neg h]
    rw [this]

theorem canon_ty (hm : 0 < m) (t : Ty m hm) : canon hm t.1 = t.1 := by
  unfold canon; rw [if_neg (by simp [t.2])]

/-- Column permutations act on the row types. -/
def tyPerm (hm : 0 < m) (π : Equiv.Perm (Fin m)) : Ty m hm ≃ Ty m hm where
  toFun t := ⟨canon hm (prow π t.1), canon_zero hm _⟩
  invFun t := ⟨canon hm (prow π⁻¹ t.1), canon_zero hm _⟩
  left_inv t := by
    apply Subtype.ext
    simp only
    rw [canon_prow_canon, prow_inv_prow, canon_ty]
  right_inv t := by
    apply Subtype.ext
    simp only
    rw [canon_prow_canon]
    have : prow π (prow π⁻¹ t.1) = t.1 := by funext k; simp [prow]
    rw [this, canon_ty]

/-! ## Column symmetry -/

/-- The rows of a tuple of types. -/
def tyRows (hm : 0 < m) {k : ℕ} (e : Fin k ↪ Ty m hm) : List (Row m) := (List.ofFn e).map Subtype.val

theorem tyRows_perm (hm : 0 < m) {k : ℕ} (π : Equiv.Perm (Fin m)) (e : Fin k ↪ Ty m hm) :
    tyRows hm (e.trans (tyPerm hm π).toEmbedding) = ((tyRows hm e).map (prow π)).map (canon hm) := by
  unfold tyRows
  simp only [List.map_ofFn]
  rfl

/-- The sum of the depth of column `j` over the separating tuples. -/
def colSum (hm : 0 < m) (k : ℕ) (j : Fin m) : ℕ :=
  ∑ e : Fin k ↪ Ty m hm, if Sep (tyRows hm e) then cdep (tyRows hm e) j else 0

theorem colSum_perm (hm : 0 < m) (k : ℕ) (π : Equiv.Perm (Fin m)) (j : Fin m) :
    colSum hm k j = colSum hm k (π j) := by
  unfold colSum
  let E : (Fin k ↪ Ty m hm) ≃ (Fin k ↪ Ty m hm) := Equiv.embeddingCongr (Equiv.refl _) (tyPerm hm π)
  have hE : ∀ e, E e = e.trans (tyPerm hm π).toEmbedding := fun e => by ext; rfl
  rw [← E.sum_comp]
  apply sum_congr rfl; intro e _
  rw [hE, tyRows_perm, sep_map_canon, sep_prow, cdep_map_canon, cdep_prow]

theorem colSum_eq (hm : 0 < m) (k : ℕ) (j : Fin m) : colSum hm k j = colSum hm k ⟨0, hm⟩ := by
  rw [colSum_perm hm k (Equiv.swap j ⟨0, hm⟩) j, Equiv.swap_apply_left]

/-- Column symmetry: `∑_{T ∈ 𝒯_k} ∑_j L_j = m ∑_{T ∈ 𝒯_k} L_0`. -/
theorem sum_ldepth_eq (hm : 0 < m) (k : ℕ) :
    ∑ e : Fin k ↪ Ty m hm, (if Sep (tyRows hm e) then ldepth (tyRows hm e) else 0) =
      m * colSum hm k ⟨0, hm⟩ := by
  have : ∀ e : Fin k ↪ Ty m hm, (if Sep (tyRows hm e) then ldepth (tyRows hm e) else 0) =
      ∑ j, (if Sep (tyRows hm e) then cdep (tyRows hm e) j else 0) := by
    intro e
    split_ifs
    · rfl
    · simp
  rw [sum_congr rfl (fun e _ => this e), sum_comm]
  show ∑ j, colSum hm k j = _
  rw [sum_congr rfl (fun j _ => colSum_eq hm k j), sum_const, card_univ, Fintype.card_fin, smul_eq_mul]

/-- `|𝒯_k|`, the number of separating `k`-tuples of distinct types. -/
def sepCount (hm : 0 < m) (k : ℕ) : ℕ := (univ.filter (fun e : Fin k ↪ Ty m hm => Sep (tyRows hm e))).card

theorem Bint_eq (hm : 0 < m) (k : ℕ) :
    Bint hm k = (m : ℤ) * colSum hm k ⟨0, hm⟩ - (sepCount hm k : ℤ) * cdepth m := by
  have h1 : Bint hm k = ∑ e : Fin k ↪ Ty m hm,
      ((if Sep (tyRows hm e) then (ldepth (tyRows hm e) : ℤ) else 0) -
        (if Sep (tyRows hm e) then (cdepth m : ℤ) else 0)) := by
    unfold Bint embSum excessT excessL
    apply sum_congr rfl; intro e _
    unfold tyRows
    split_ifs <;> simp
  have h3 : ∑ e : Fin k ↪ Ty m hm, (if Sep (tyRows hm e) then (cdepth m : ℤ) else 0) =
      (sepCount hm k : ℤ) * cdepth m := by
    rw [← sum_filter, sum_const, nsmul_eq_mul]
    rfl
  rw [h1, sum_sub_distrib, h3]
  have h2 : ∑ e : Fin k ↪ Ty m hm, (if Sep (tyRows hm e) then (ldepth (tyRows hm e) : ℤ) else 0) =
      ((∑ e : Fin k ↪ Ty m hm, (if Sep (tyRows hm e) then ldepth (tyRows hm e) else 0) : ℕ) : ℤ) := by
    push_cast
    apply sum_congr rfl; intro e _
    split_ifs <;> simp
  rw [h2, sum_ldepth_eq]
  push_cast
  ring

/-! ## The representative tables and the free action -/

/-- Tables of `k` rows of pairwise distinct types that separate the columns. -/
def RepTable (m : ℕ) (hm : 0 < m) (k : ℕ) : Type :=
  {A : Table k m // Function.Injective (fun i => canon hm (A i)) ∧ Sep (List.ofFn A)}

noncomputable instance (hm : 0 < m) (k : ℕ) : Fintype (RepTable m hm k) := by
  unfold RepTable; infer_instance

theorem sep_ofFn_iff (hm : 0 < m) {k : ℕ} (A : Table k m) (τ : Fin k → Ty m hm)
    (h : ∀ i, canon hm (A i) = (τ i).1) : Sep (List.ofFn A) ↔ Sep ((List.ofFn τ).map Subtype.val) := by
  rw [← sep_map_canon hm, List.map_ofFn, List.map_ofFn]
  have : canon hm ∘ A = Subtype.val ∘ τ := funext h
  rw [this]

theorem rowsEquiv_symm_canon (hm : 0 < m) {k : ℕ} (τ : Fin k → Ty m hm) (o : Fin k → Bool) (i : Fin k) :
    canon hm ((rowsEquiv hm).symm (τ, o) i) = (τ i).1 := by
  have := congrArg (fun p => (p.1 i).1) ((rowsEquiv hm).apply_symm_apply (τ, o))
  exact this

/-- A representative table is a separating tuple of types and an orientation of each row. -/
def repEquiv (hm : 0 < m) (k : ℕ) :
    RepTable m hm k ≃ {e : Fin k ↪ Ty m hm // Sep (tyRows hm e)} × (Fin k → Bool) where
  toFun A := (⟨⟨fun i => ⟨canon hm (A.1 i), canon_zero hm _⟩, fun a b h => A.2.1 (congrArg Subtype.val h)⟩,
      (sep_ofFn_iff hm A.1 _ (fun i => rfl)).mp A.2.2⟩, fun i => A.1 i ⟨0, hm⟩)
  invFun p := ⟨(rowsEquiv hm).symm (p.1.1, p.2), by
      refine ⟨fun a b h => ?_, ?_⟩
      · simp only [rowsEquiv_symm_canon] at h
        exact p.1.1.injective (Subtype.ext h)
      · exact (sep_ofFn_iff hm _ p.1.1 (rowsEquiv_symm_canon hm _ _)).mpr p.1.2⟩
  left_inv A := Subtype.ext ((rowsEquiv hm).left_inv A.1)
  right_inv p := by
    obtain ⟨⟨e, he⟩, o⟩ := p
    have h := (rowsEquiv hm).right_inv (⇑e, o)
    refine Prod.ext (Subtype.ext (Function.Embedding.ext fun i => ?_)) ?_
    · exact congrFun (congrArg Prod.fst h) i
    · show (fun i => ((rowsEquiv hm).symm (⇑e, o)) i ⟨0, hm⟩) = o
      exact congrArg Prod.snd h

theorem card_repTable (hm : 0 < m) (k : ℕ) : Fintype.card (RepTable m hm k) = sepCount hm k * 2 ^ k := by
  rw [Fintype.card_congr (repEquiv hm k), Fintype.card_prod, Fintype.card_subtype, Fintype.card_fun,
    Fintype.card_bool, Fintype.card_fin]
  rfl

/-- Column permutations act on the representative tables: `π • A` has rows `r ∘ π⁻¹`. -/
instance repAction (hm : 0 < m) (k : ℕ) : MulAction (Equiv.Perm (Fin m)) (RepTable m hm k) where
  smul π A := ⟨fun i => prow π⁻¹ (A.1 i), by
    refine ⟨fun a b h => ?_, ?_⟩
    · simp only at h
      apply A.2.1
      simp only
      rw [← prow_inv_prow π⁻¹ (A.1 a), ← prow_inv_prow π⁻¹ (A.1 b), ← canon_prow_canon,
        ← canon_prow_canon hm (π⁻¹)⁻¹ (prow π⁻¹ (A.1 b)), h]
    · have := (sep_prow π⁻¹ (List.ofFn A.1)).mpr A.2.2
      rw [List.map_ofFn] at this
      exact this⟩
  one_smul A := by
    apply Subtype.ext; funext i k; rfl
  mul_smul σ π A := by
    apply Subtype.ext; funext i
    show prow (σ * π)⁻¹ (A.1 i) = prow σ⁻¹ (prow π⁻¹ (A.1 i))
    rw [mul_inv_rev]
    funext k; simp [prow]

theorem repAction_free (hm : 0 < m) (k : ℕ) (π : Equiv.Perm (Fin m)) (A : RepTable m hm k)
    (h : π • A = A) : π = 1 := by
  have hA : ∀ i c, A.1 i (π⁻¹ c) = A.1 i c := by
    intro i c
    have := congrFun (congrFun (congrArg Subtype.val h) i) c
    exact this
  have hc : ∀ c, π⁻¹ c = c := by
    intro c
    by_contra hne
    obtain ⟨r, hr, hd⟩ := A.2.2 _ _ hne
    obtain ⟨i, rfl⟩ := List.mem_ofFn.mp hr
    exact hd (hA i c)
  have : π⁻¹ = 1 := Equiv.ext hc
  rw [← inv_inv π, this, inv_one]

/-- `m! ∣ 2^k |𝒯_k|`: the column permutations act freely on the representative tables. -/
theorem factorial_dvd_card (hm : 0 < m) (k : ℕ) : m.factorial ∣ 2 ^ k * sepCount hm k := by
  have hstab : ∀ A : RepTable m hm k,
      Fintype.card (MulAction.stabilizer (Equiv.Perm (Fin m)) A) = 1 := by
    intro A
    rw [Fintype.card_eq_one_iff]
    refine ⟨⟨1, MulAction.mem_stabilizer_iff.mpr (one_smul _ A)⟩, fun y => Subtype.ext ?_⟩
    exact repAction_free hm k y.1 A (MulAction.mem_stabilizer_iff.mp y.2)
  have hcard := MulAction.card_eq_sum_card_group_div_card_stabilizer (Equiv.Perm (Fin m)) (RepTable m hm k)
  rw [card_repTable] at hcard
  rw [mul_comm, hcard]
  apply dvd_sum; intro ω _
  rw [hstab, Nat.div_one, Fintype.card_perm, Fintype.card_fin]

/-! ## Arithmetic -/

theorem cdepth_int (hm : 0 < m) :
    (cdepth m : ℤ) = m * (Nat.log 2 m + 2) - 2 ^ (Nat.log 2 m + 1) := by
  unfold cdepth
  have h := Nat.pow_log_le_self 2 hm.ne'
  have : 2 ^ (Nat.log 2 m + 1) ≤ m * (Nat.log 2 m + 2) := by
    rw [pow_succ]; nlinarith
  push_cast [Nat.cast_sub this]
  ring

/-- The odd part of `m` divides `|𝒯_k|`. -/
theorem ordCompl_dvd_sepCount (hm : 0 < m) (k : ℕ) : ordCompl[2] m ∣ sepCount hm k := by
  have h1 : ordCompl[2] m ∣ 2 ^ k * sepCount hm k :=
    (Nat.ordCompl_dvd m 2).trans ((Nat.dvd_factorial hm le_rfl).trans (factorial_dvd_card hm k))
  have hc : Nat.Coprime (ordCompl[2] m) (2 ^ k) :=
    (Nat.Coprime.pow_left k (Nat.coprime_ordCompl Nat.prime_two hm.ne')).symm
  exact hc.dvd_of_dvd_mul_left h1

/-- `m ∣ |𝒯_k| · cdepth m`. -/
theorem dvd_sepCount_cdepth (hm : 0 < m) (k : ℕ) : (m : ℤ) ∣ (sepCount hm k : ℤ) * cdepth m := by
  rw [cdepth_int hm]
  have h2 : (m : ℤ) ∣ (sepCount hm k : ℤ) * 2 ^ (Nat.log 2 m + 1) := by
    have ha : ordProj[2] m ∣ 2 ^ (Nat.log 2 m + 1) := by
      apply Nat.pow_dvd_pow
      have := Nat.le_log_of_pow_le (by norm_num) (Nat.ordProj_le 2 hm.ne')
      omega
    have hmul : ordProj[2] m * ordCompl[2] m ∣ 2 ^ (Nat.log 2 m + 1) * sepCount hm k :=
      Nat.mul_dvd_mul ha (ordCompl_dvd_sepCount hm k)
    rw [Nat.ordProj_mul_ordCompl_eq_self] at hmul
    have := Int.natCast_dvd_natCast.mpr hmul
    push_cast at this
    rw [mul_comm]; exact this
  have h3 : (m : ℤ) ∣ (sepCount hm k : ℤ) * (m * (Nat.log 2 m + 2)) :=
    Dvd.intro ((sepCount hm k : ℤ) * (Nat.log 2 m + 2)) (by ring)
  rw [mul_sub]
  exact dvd_sub h3 h2

/-- `m ∣ m B_k`. -/
theorem Bint_dvd (hm : 0 < m) (k : ℕ) : (m : ℤ) ∣ Bint hm k := by
  rw [Bint_eq]
  exact dvd_sub (Dvd.intro _ rfl) (dvd_sepCount_cdepth hm k)

/-- The `B_k` are integers. -/
theorem Bk_integer (hm : 0 < m) (k : ℕ) : ∃ z : ℤ, Bk hm k = z := by
  obtain ⟨z, hz⟩ := Bint_dvd hm k
  refine ⟨z, ?_⟩
  unfold Bk
  rw [hz]
  have : (m : ℝ) ≠ 0 := by exact_mod_cast hm.ne'
  push_cast
  field_simp

end GradientKey.Concrete
