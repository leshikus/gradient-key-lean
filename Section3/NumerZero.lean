import SmallItems

/-!
# `N_m(0) = 0`

The constant row type never changes the tree of `G`. Inserting it at the `k + 1` places of a `k`-tuple without it
gives the `(k+1)`-tuples with it, so `B_{k+1} = B'_{k+1} + (k+1) B'_k`, where `B'_k` sums over the tuples without
the constant row type. Hence `∑_k (-1)^k B_k / k! = 0` and `N_m(0) = ∑_j a_j = 0`.
-/

noncomputable section

namespace GradientKey.Concrete
open Classical Finset

variable {m : ℕ}

/-! ## A row of quality `0` inserted into a row list -/

theorem argmax_insert_zero {α : Type*} (f : α → ℕ) (l1 : List α) (a : α) (ha : f a = 0) (l2 : List α) :
    List.argmax f (l1 ++ a :: l2) = List.argmax f (l1 ++ l2) ∨ ∀ x ∈ l1 ++ l2, f x = 0 := by
  induction l2 using List.reverseRecOn with
  | nil =>
    rw [List.append_nil, List.argmax_concat]
    cases hc : List.argmax f l1 with
    | none =>
      right
      intro x hx
      exact absurd (List.argmax_eq_none.mp hc) (List.ne_nil_of_mem hx)
    | some c =>
      left
      simp [ha]
  | append_singleton l2 b ih =>
    rw [show l1 ++ a :: (l2 ++ [b]) = (l1 ++ a :: l2) ++ [b] by simp,
      show l1 ++ (l2 ++ [b]) = (l1 ++ l2) ++ [b] by simp, List.argmax_concat, List.argmax_concat]
    rcases ih with h | h
    · left; rw [h]
    · by_cases hb : f b = 0
      · right
        intro x hx
        rcases List.mem_append.mp hx with hx | hx
        · exact h x hx
        · rw [List.mem_singleton.mp hx]; exact hb
      · left
        have hbpos : 0 < f b := Nat.pos_of_ne_zero hb
        have h' : ∀ x ∈ l1 ++ a :: l2, f x = 0 := by
          intro x hx
          rcases List.mem_append.mp hx with hx | hx
          · exact h x (List.mem_append_left _ hx)
          · rcases List.mem_cons.mp hx with hx | hx
            · rw [hx]; exact ha
            · exact h x (List.mem_append_right _ hx)
        cases hc1 : List.argmax f (l1 ++ a :: l2) with
        | none =>
          cases hc2 : List.argmax f (l1 ++ l2) with
          | none => rfl
          | some c2 =>
            have : f c2 = 0 := h c2 (List.argmax_mem hc2)
            simp [this, hbpos]
        | some c1 =>
          have h1 : f c1 = 0 := h' c1 (List.argmax_mem hc1)
          cases hc2 : List.argmax f (l1 ++ l2) with
          | none => simp [h1, hbpos]
          | some c2 =>
            have : f c2 = 0 := h c2 (List.argmax_mem hc2)
            simp [this, h1, hbpos]

theorem filter_const_of_rq_zero (S : Finset (Fin m)) (r : Row m) (j : Fin m) (hj : j ∈ S)
    (h : rq S r = 0) : S.filter (fun k => r k = r j) = S := by
  apply Finset.filter_true_of_mem
  intro k hk
  unfold rq at h
  rcases Nat.min_eq_zero_iff.mp h with h0 | h0 <;>
  · rw [Finset.card_eq_zero, Finset.filter_eq_empty_iff] at h0
    have h1 := h0 hk
    have h2 := h0 hj
    cases hrk : r k <;> cases hrj : r j <;> simp_all

def constRow (m : ℕ) : Row m := fun _ => false

theorem rq_constRow (S : Finset (Fin m)) : rq S (constRow m) = 0 := by
  unfold rq constRow; simp

theorem lstep_mem (L : List (Row m)) (S : Finset (Fin m)) (j : Fin m) (hj : j ∈ S) :
    j ∈ lstep L S j := by
  unfold lstep
  split_ifs
  · exact hj
  · split
    · exact hj
    · simp [hj]

theorem lcand_mem (L : List (Row m)) (j : Fin m) (i : ℕ) : j ∈ lcand L j i := by
  induction i with
  | zero => simp [lcand]
  | succ i ih =>
    unfold lcand at ih ⊢
    rw [Function.iterate_succ_apply']
    exact lstep_mem L _ j ih

theorem lstep_insert_const (l1 l2 : List (Row m)) (S : Finset (Fin m)) (j : Fin m) (hj : j ∈ S) :
    lstep (l1 ++ constRow m :: l2) S j = lstep (l1 ++ l2) S j := by
  unfold lstep
  split_ifs with hS
  · rfl
  rcases argmax_insert_zero (rq S) l1 _ (rq_constRow S) l2 with h | h
  · rw [h]
  · have h' : ∀ x ∈ l1 ++ constRow m :: l2, rq S x = 0 := by
      intro x hx
      rcases List.mem_append.mp hx with hx | hx
      · exact h x (List.mem_append_left _ hx)
      · rcases List.mem_cons.mp hx with hx | hx
        · rw [hx]; exact rq_constRow S
        · exact h x (List.mem_append_right _ hx)
    cases hc1 : List.argmax (rq S) (l1 ++ constRow m :: l2) with
    | none =>
      cases hc2 : List.argmax (rq S) (l1 ++ l2) with
      | none => rfl
      | some c2 =>
        exact (filter_const_of_rq_zero S c2 j hj (h c2 (List.argmax_mem hc2))).symm
    | some c1 =>
      dsimp only
      rw [filter_const_of_rq_zero S c1 j hj (h' c1 (List.argmax_mem hc1))]
      cases hc2 : List.argmax (rq S) (l1 ++ l2) with
      | none => rfl
      | some c2 =>
        exact (filter_const_of_rq_zero S c2 j hj (h c2 (List.argmax_mem hc2))).symm

theorem ldepth_insert_const (l1 l2 : List (Row m)) :
    ldepth (l1 ++ constRow m :: l2) = ldepth (l1 ++ l2) := by
  have hc : ∀ j i, lcand (l1 ++ constRow m :: l2) j i = lcand (l1 ++ l2) j i := by
    intro j i
    induction i with
    | zero => rfl
    | succ i ih =>
      unfold lcand at ih ⊢
      rw [Function.iterate_succ_apply', Function.iterate_succ_apply', ← ih]
      apply lstep_insert_const
      have := lcand_mem (l1 ++ constRow m :: l2) j i
      unfold lcand at this
      exact this
  unfold ldepth
  simp only [hc]

theorem sep_insert_const (l1 l2 : List (Row m)) :
    Sep (l1 ++ constRow m :: l2) ↔ Sep (l1 ++ l2) := by
  unfold Sep
  constructor
  · intro h j k hjk
    obtain ⟨r, hr, hne⟩ := h j k hjk
    refine ⟨r, ?_, hne⟩
    rcases List.mem_append.mp hr with hr | hr
    · exact List.mem_append_left _ hr
    · rcases List.mem_cons.mp hr with hr | hr
      · exact absurd (by rw [hr]; rfl) hne
      · exact List.mem_append_right _ hr
  · intro h j k hjk
    obtain ⟨r, hr, hne⟩ := h j k hjk
    refine ⟨r, ?_, hne⟩
    rcases List.mem_append.mp hr with hr | hr
    · exact List.mem_append_left _ hr
    · exact List.mem_append_right _ (List.mem_cons_of_mem _ hr)

theorem excessL_insert_const (l1 l2 : List (Row m)) :
    excessL m (l1 ++ constRow m :: l2) = excessL m (l1 ++ l2) := by
  unfold excessL
  rw [ldepth_insert_const]
  by_cases h : Sep (l1 ++ l2)
  · rw [if_pos ((sep_insert_const l1 l2).mpr h), if_pos h]
  · rw [if_neg (fun h' => h ((sep_insert_const l1 l2).mp h')), if_neg h]

/-! ## Tuples with the constant row type -/

theorem ofFn_insertNth {α : Type*} {k : ℕ} (p : Fin (k + 1)) (a : α) (f : Fin k → α) :
    List.ofFn (Fin.insertNth p a f) = (List.ofFn f).take p ++ a :: (List.ofFn f).drop p := by
  have hp := p.isLt
  have hlen : ((List.ofFn f).take p).length = p := by simp; omega
  apply List.ext_getElem
  · simp; omega
  · intro i h1' h2
    have h1 : i < k + 1 := by simpa using h1'
    rw [List.getElem_ofFn]
    rcases lt_trichotomy i p with hi | hi | hi
    · have e : (⟨i, h1⟩ : Fin (k + 1)) = p.succAbove ⟨i, by omega⟩ := by
        rw [Fin.succAbove_of_castSucc_lt _ _ (by simp [Fin.lt_def]; omega)]; rfl
      rw [e, Fin.insertNth_apply_succAbove, List.getElem_append_left (by rw [hlen]; exact hi)]
      simp
    · have e : (⟨i, h1⟩ : Fin (k + 1)) = p := Fin.ext hi
      rw [e, Fin.insertNth_apply_same, List.getElem_append_right (by rw [hlen]; omega)]
      simp [hlen, hi]
    · have e : (⟨i, h1⟩ : Fin (k + 1)) = p.succAbove ⟨i - 1, by omega⟩ := by
        rw [Fin.succAbove_of_le_castSucc _ _ (by simp [Fin.le_def]; omega)]
        ext; simp; omega
      rw [e, Fin.insertNth_apply_succAbove, List.getElem_append_right (by rw [hlen]; omega)]
      have hi' : i - ((List.ofFn f).take p).length = (i - 1 - p) + 1 := by rw [hlen]; omega
      simp only [hi', List.getElem_cons_succ, List.getElem_drop, List.getElem_ofFn]
      congr 1; ext; simp; omega

/-- The constant row type. -/
def c0 (hm : 0 < m) : Ty m hm := ⟨constRow m, rfl⟩

theorem excessT_insert_c0 (hm : 0 < m) {k : ℕ} (p : Fin (k + 1)) (f : Fin k → Ty m hm) :
    excessT hm (List.ofFn (Fin.insertNth p (c0 hm) f)) = excessT hm (List.ofFn f) := by
  unfold excessT
  rw [ofFn_insertNth]
  simp only [List.map_append, List.map_cons, List.map_take, List.map_drop]
  rw [show (c0 hm).val = constRow m from rfl, excessL_insert_const, List.take_append_drop]

/-- `B'_k`: the sum over the `k`-tuples of distinct row types without the constant row type. -/
def Bavoid (hm : 0 < m) (k : ℕ) : ℤ :=
  ∑ e : {e : Fin k ↪ Ty m hm // c0 hm ∉ Set.range e}, excessT hm (List.ofFn e.1)

/-- Insert the constant row type at place `p`. -/
def insC0 (hm : 0 < m) {k : ℕ} (q : Fin (k + 1) × {e : Fin k ↪ Ty m hm // c0 hm ∉ Set.range e}) :
    {e : Fin (k + 1) ↪ Ty m hm // c0 hm ∈ Set.range e} :=
  ⟨⟨Fin.insertNth q.1 (c0 hm) q.2.1, by
    intro x y hxy
    have he := q.2.2
    rcases Fin.eq_self_or_eq_succAbove q.1 x with hx | ⟨i, hx⟩ <;>
    rcases Fin.eq_self_or_eq_succAbove q.1 y with hy | ⟨j, hy⟩ <;> subst hx <;> subst hy
    · rfl
    · simp only [Fin.insertNth_apply_same, Fin.insertNth_apply_succAbove] at hxy
      exact (he ⟨j, hxy.symm⟩).elim
    · simp only [Fin.insertNth_apply_same, Fin.insertNth_apply_succAbove] at hxy
      exact (he ⟨i, hxy⟩).elim
    · simp only [Fin.insertNth_apply_succAbove] at hxy
      rw [q.2.1.injective hxy]⟩, ⟨q.1, Fin.insertNth_apply_same (α := fun _ => Ty m hm) q.1 (c0 hm) q.2.1⟩⟩

theorem insC0_apply (hm : 0 < m) {k : ℕ} (q : Fin (k + 1) × {e : Fin k ↪ Ty m hm // c0 hm ∉ Set.range e}) :
    ((insC0 hm q).1 : Fin (k + 1) → Ty m hm) = Fin.insertNth q.1 (c0 hm) q.2.1 := rfl

theorem insC0_bijective (hm : 0 < m) (k : ℕ) : Function.Bijective (insC0 hm (k := k)) := by
  constructor
  · rintro ⟨p, e, he⟩ ⟨p', e', he'⟩ h
    have h1 : (Fin.insertNth p (c0 hm) e : Fin (k + 1) → Ty m hm) = Fin.insertNth p' (c0 hm) e' := by
      have := congrArg (fun z => ((z.1 : Fin (k + 1) ↪ Ty m hm) : Fin (k + 1) → Ty m hm)) h
      simpa only [insC0_apply] using this
    have hpp : p = p' := by
      have h2 := congrFun h1 p
      rw [Fin.insertNth_apply_same] at h2
      rcases Fin.eq_self_or_eq_succAbove p' p with hp | ⟨i, hp⟩
      · exact hp
      · rw [hp, Fin.insertNth_apply_succAbove] at h2
        exact (he' ⟨i, h2.symm⟩).elim
    subst hpp
    have h3 := congrArg (Fin.removeNth p) h1
    simp only [Fin.removeNth_insertNth] at h3
    have : e = e' := Function.Embedding.ext (fun i => congrFun h3 i)
    subst this
    rfl
  · rintro ⟨e, he⟩
    obtain ⟨p, hp⟩ := he
    refine ⟨(p, ⟨⟨fun i => e (p.succAbove i), e.injective.comp (Fin.succAbove_right_injective)⟩, ?_⟩), ?_⟩
    · rintro ⟨i, hi⟩
      exact Fin.succAbove_ne p i (e.injective (hi.trans hp.symm))
    · apply Subtype.ext
      apply Function.Embedding.ext
      intro x
      rw [insC0_apply]
      show (Fin.insertNth p (c0 hm) (fun i => e (p.succAbove i)) : Fin (k + 1) → Ty m hm) x = e x
      rcases Fin.eq_self_or_eq_succAbove p x with hx | ⟨i, hx⟩
      · rw [hx, Fin.insertNth_apply_same, hp]
      · rw [hx, Fin.insertNth_apply_succAbove]

theorem Bint_succ_split (hm : 0 < m) (k : ℕ) :
    Bint hm (k + 1) = Bavoid hm (k + 1) + (k + 1) * Bavoid hm k := by
  unfold Bint embSum
  rw [← Fintype.sum_subtype_add_sum_subtype (fun e : Fin (k + 1) ↪ Ty m hm => c0 hm ∈ Set.range e)]
  rw [add_comm]
  congr 1
  rw [← Fintype.sum_bijective (insC0 hm) (insC0_bijective hm k)
    (fun q => excessT hm (List.ofFn q.2.1)) (fun e => excessT hm (List.ofFn e.1))
    (fun q => by rw [insC0_apply, excessT_insert_c0])]
  rw [Fintype.sum_prod_type]
  simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
  unfold Bavoid
  push_cast
  ring

theorem Bint_zero (hm2 : 2 ≤ m) : Bint (by omega : 0 < m) 0 = 0 := by
  unfold Bint embSum
  exact Finset.sum_eq_zero (fun e _ => excessT_emb_zero hm2 e)

theorem Bavoid_zero (hm2 : 2 ≤ m) : Bavoid (by omega : 0 < m) 0 = 0 := by
  unfold Bavoid
  exact Finset.sum_eq_zero (fun e _ => excessT_emb_zero hm2 e.1)

theorem Bavoid_numTypes (hm : 0 < m) : Bavoid hm (numTypes hm) = 0 := by
  unfold Bavoid
  apply Finset.sum_eq_zero
  rintro ⟨e, he⟩ _
  exfalso
  apply he
  have hb := (Fintype.bijective_iff_injective_and_card e).mpr ⟨e.injective, by unfold numTypes; convert Fintype.card_fin _⟩
  exact hb.2 (c0 hm)

/-- `∑_{k=0}^{M} (-1)^k B_k / k! = 0`. -/
theorem alt_sum_Bint (hm2 : 2 ≤ m) :
    ∑ k ∈ range (numTypes (by omega : 0 < m) + 1),
      (-1 : ℝ) ^ k * (Bint (by omega : 0 < m) k : ℝ) / k.factorial = 0 := by
  have hm : 0 < m := by omega
  set u : ℕ → ℝ := fun k => (-1 : ℝ) ^ k * (Bavoid hm k : ℝ) / k.factorial with hu
  rw [Finset.sum_range_succ']
  have hstep : ∀ k, (-1 : ℝ) ^ (k + 1) * (Bint hm (k + 1) : ℝ) / (k + 1).factorial = u (k + 1) - u k := by
    intro k
    rw [Bint_succ_split hm k, hu]
    simp only [Nat.factorial_succ]
    push_cast
    have hf : (k.factorial : ℝ) ≠ 0 := by positivity
    field_simp
    ring
  simp only [hstep]
  rw [Finset.sum_range_sub, Bint_zero hm2]
  simp only [hu, Bavoid_numTypes hm, Bavoid_zero hm2]
  simp

/-- `N_m(0) = ∑_{j=1}^{M} a_j = 0` for `m ≥ 2`. -/
theorem numer_zero (hm2 : 2 ≤ m) : numer (by omega : 0 < m) 0 = 0 := by
  have hm : 0 < m := by omega
  set M := numTypes hm
  -- the inner alternating sum
  have hinner : ∀ k ∈ range (M + 1),
      ∑ j ∈ Icc 1 M, (-1 : ℝ) ^ (k - j) * (k.choose j : ℝ) = (0 : ℝ) ^ k - (-1 : ℝ) ^ k := by
    intro k hk
    have hkM : k ≤ M := Nat.lt_succ_iff.mp (Finset.mem_range.mp hk)
    have hfull : ∑ j ∈ range (M + 1), (-1 : ℝ) ^ (k - j) * (k.choose j : ℝ) = (0 : ℝ) ^ k := by
      rw [← Finset.sum_subset (Finset.range_subset_range.mpr (Nat.succ_le_succ hkM))]
      · have h := stirT_zero k
        unfold stirT at h
        have hz := congrArg (fun z : ℤ => (z : ℝ)) h
        push_cast at hz
        simpa using hz
      · intro j hj hj'
        have : k < j := by simp at hj hj'; omega
        simp [Nat.choose_eq_zero_of_lt this]
    have hsplit : ∑ j ∈ range (M + 1), (-1 : ℝ) ^ (k - j) * (k.choose j : ℝ) =
        ∑ j ∈ Icc 1 M, (-1 : ℝ) ^ (k - j) * (k.choose j : ℝ) + (-1 : ℝ) ^ k := by
      rw [Finset.sum_range_succ', ← Finset.Ico_add_one_right_eq_Icc, Finset.sum_Ico_eq_sum_range]
      simp [add_comm]
    linarith
  unfold numer coeffA
  simp only [pow_zero, mul_one]
  rw [Finset.sum_comm]
  have hterm : ∀ k ∈ range (M + 1),
      ∑ j ∈ Icc 1 M, (-1 : ℝ) ^ (k - j) * (k.choose j : ℝ) * Bk hm k / k.factorial =
        -((-1 : ℝ) ^ k * (Bint hm k : ℝ) / k.factorial) / m := by
    intro k hk
    have : ∑ j ∈ Icc 1 M, (-1 : ℝ) ^ (k - j) * (k.choose j : ℝ) * Bk hm k / k.factorial =
        (∑ j ∈ Icc 1 M, (-1 : ℝ) ^ (k - j) * (k.choose j : ℝ)) * (Bk hm k / k.factorial) := by
      rw [Finset.sum_mul]; apply Finset.sum_congr rfl; intro j _; ring
    rw [this, hinner k hk]
    rcases Nat.eq_zero_or_pos k with rfl | hk0
    · rw [Bint_zero hm2]; simp
    · rw [zero_pow hk0.ne']
      unfold Bk
      ring
  rw [Finset.sum_congr rfl hterm, ← Finset.sum_div, Finset.sum_neg_distrib, alt_sum_Bint hm2]
  simp

end GradientKey.Concrete
