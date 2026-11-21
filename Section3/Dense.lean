import TreeDepth

/-!
# Proposition 3.4 (`prop:dense`)

If `n ≥ 1` and `2^n - n ≤ m ≤ 2^n`, then `L̄(G(A)) = C(m)` for every `A ∈ 𝒜_{n,m}`; so `t_{n,m}(G) = C(m)`.

The proof works with the total depth `D(S) = ∑_{j ∈ S} (forks below S on the path of j)`. A candidate set `S`
whose columns agree outside a set `F` of `k` rows, with `2^k ≤ |S| + k` (at most `k` missing words), has
`D(S) = cdepth |S|`, the total depth of the complete tree on `|S|` leaves.
-/

noncomputable section

namespace GradientKey.Concrete

open Finset

variable {n m : ℕ}

/-- Total leaf depth of the complete tree on `s` leaves: `s (ℓ + 2) - 2^(ℓ+1)`, `ℓ = ⌊log₂ s⌋`. -/
def cdepth (s : ℕ) : ℕ := s * (Nat.log 2 s + 2) - 2 ^ (Nat.log 2 s + 1)

/-- `C(m) = ℓ + 2 - 2^(ℓ+1)/m`, the cost of the complete tree on `m` leaves. -/
def completeCost (m : ℕ) : ℝ := (Nat.log 2 m : ℝ) + 2 - 2 ^ (Nat.log 2 m + 1) / (m : ℝ)

theorem cdepth_eq (h s : ℕ) (h1 : 2 ^ h ≤ s) (h2 : s ≤ 2 ^ (h + 1)) :
    cdepth s = s * (h + 2) - 2 ^ (h + 1) := by
  unfold cdepth
  rcases lt_or_eq_of_le h2 with hlt | heq
  · rw [Nat.log_eq_of_pow_le_of_lt_pow h1 hlt]
  · subst heq
    rw [Nat.log_pow (by norm_num)]
    rw [show 2 ^ (h + 1 + 1) = 2 ^ (h + 1) * 2 by ring]
    have : 2 ^ (h + 1) * 2 ≤ 2 ^ (h + 1) * (h + 1 + 2) := Nat.mul_le_mul_left _ (by omega)
    have : 2 ^ (h + 1) ≤ 2 ^ (h + 1) * (h + 2) := Nat.le_mul_of_pos_right _ (by omega)
    zify [*]
    ring

theorem cdepth_add (h a b : ℕ) (ha1 : 2 ^ h ≤ a) (ha2 : a ≤ 2 ^ (h + 1))
    (hb1 : 2 ^ h ≤ b) (hb2 : b ≤ 2 ^ (h + 1)) :
    cdepth a + cdepth b + (a + b) = cdepth (a + b) := by
  have hp : 2 ^ (h + 1) = 2 * 2 ^ h := by ring
  have hp2 : 2 ^ (h + 1 + 1) = 2 * 2 ^ (h + 1) := by ring
  rw [cdepth_eq h a ha1 ha2, cdepth_eq h b hb1 hb2,
    cdepth_eq (h + 1) (a + b) (by omega) (by omega)]
  have e1 : 2 ^ (h + 1) ≤ a * (h + 2) := by
    calc 2 ^ (h + 1) = 2 * 2 ^ h := hp
      _ ≤ 2 * a := by omega
      _ ≤ a * (h + 2) := by nlinarith
  have e2 : 2 ^ (h + 1) ≤ b * (h + 2) := by
    calc 2 ^ (h + 1) = 2 * 2 ^ h := hp
      _ ≤ 2 * b := by omega
      _ ≤ b * (h + 2) := by nlinarith
  have e3 : 2 ^ (h + 1 + 1) ≤ (a + b) * (h + 1 + 2) := by
    calc 2 ^ (h + 1 + 1) = 2 * 2 ^ (h + 1) := hp2
      _ ≤ 2 * (a + b) := by omega
      _ ≤ (a + b) * (h + 1 + 2) := by nlinarith
  zify [e1, e2, e3]
  ring

theorem le_two_pow_pred (k : ℕ) (hk : 1 ≤ k) : k ≤ 2 ^ (k - 1) := by
  obtain ⟨t, rfl⟩ : ∃ t, k = t + 1 := ⟨k - 1, by omega⟩
  simpa using Nat.lt_two_pow_self (n := t)

/-- The pattern of column `j` on the rows of `F`. -/
def pat (A : Table n m) (F : Finset (Fin n)) (j : Fin m) : F → Bool := fun x => A x.1 j

/-- Columns of `S` agree on every row outside `F`. -/
def AgreeOff (A : Table n m) (F : Finset (Fin n)) (S : Finset (Fin m)) : Prop :=
  ∀ j ∈ S, ∀ j' ∈ S, ∀ r ∉ F, A r j = A r j'

theorem pat_injOn (A : Table n m) (hA : DistinctColumns A) (F : Finset (Fin n))
    (S : Finset (Fin m)) (hS : AgreeOff A F S) : Set.InjOn (pat A F) S := by
  intro j hj j' hj' he
  apply hA
  funext r
  by_cases hr : r ∈ F
  · exact congrFun he ⟨r, hr⟩
  · exact hS j hj j' hj' r hr

theorem card_le_two_pow (A : Table n m) (hA : DistinctColumns A) (F : Finset (Fin n))
    (S : Finset (Fin m)) (hS : AgreeOff A F S) : S.card ≤ 2 ^ F.card := by
  classical
  have := Finset.card_le_card_of_injOn (pat A F) (t := (univ : Finset (F → Bool)))
    (fun _ _ => mem_univ _) (pat_injOn A hA F S hS)
  simpa [Fintype.card_fun, Fintype.card_coe] using this

/-- The columns of `S` with bit `b` in row `c`. -/
def slice (A : Table n m) (S : Finset (Fin m)) (c : Fin n) (b : Bool) : Finset (Fin m) :=
  S.filter (fun k => A c k = b)

/-- The pattern of column `j` on `F \ {c}`. -/
def patE (A : Table n m) (F : Finset (Fin n)) (c : Fin n) (j : Fin m) : (F.erase c) → Bool :=
  fun x => A x.1 j

theorem patE_injOn (A : Table n m) (hA : DistinctColumns A) (F : Finset (Fin n))
    (S : Finset (Fin m)) (hS : AgreeOff A F S) (c : Fin n) (b : Bool) :
    Set.InjOn (patE A F c) (slice A S c b) := by
  intro j hj j' hj' he
  simp only [slice, coe_filter, Set.mem_setOf_eq] at hj hj'
  apply hA
  funext r
  by_cases hrc : r = c
  · subst hrc; show A r j = A r j'; rw [hj.2, hj'.2]
  by_cases hr : r ∈ F
  · exact congrFun he ⟨r, mem_erase.mpr ⟨hrc, hr⟩⟩
  · exact hS j hj.1 j' hj'.1 r hr

theorem slice_card_le (A : Table n m) (hA : DistinctColumns A) (F : Finset (Fin n))
    (S : Finset (Fin m)) (hS : AgreeOff A F S) (c : Fin n) (hc : c ∈ F) (b : Bool) :
    (slice A S c b).card ≤ 2 ^ (F.card - 1) := by
  classical
  have := Finset.card_le_card_of_injOn (patE A F c) (t := (univ : Finset ((F.erase c) → Bool)))
    (fun _ _ => mem_univ _) (patE_injOn A hA F S hS c b)
  rwa [card_univ, Fintype.card_fun, Fintype.card_coe, card_erase_of_mem hc,
    Fintype.card_bool] at this

theorem slice_card_add (A : Table n m) (S : Finset (Fin m)) (c : Fin n) :
    (slice A S c true).card + (slice A S c false).card = S.card := by
  have := Finset.card_filter_add_card_filter_not (s := S) (fun k => A c k = true)
  simpa [slice] using this

/-- A full slice realizes every pattern with bit `b` at `c`. -/
theorem full_slice_hits (A : Table n m) (hA : DistinctColumns A) (F : Finset (Fin n))
    (S : Finset (Fin m)) (hS : AgreeOff A F S) (c : Fin n) (hc : c ∈ F) (b : Bool)
    (hfull : (slice A S c b).card = 2 ^ (F.card - 1)) (p : F → Bool) (hp : p ⟨c, hc⟩ = b) :
    ∃ j ∈ S, pat A F j = p := by
  classical
  let I := (slice A S c b).image (patE A F c)
  have hI : I = univ := by
    apply Finset.eq_univ_of_card
    rw [Finset.card_image_of_injOn (patE_injOn A hA F S hS c b), hfull, Fintype.card_fun,
      Fintype.card_coe, card_erase_of_mem hc, Fintype.card_bool]
  have hq : (fun y : (F.erase c) => p ⟨y.1, mem_of_mem_erase y.2⟩) ∈ I := by rw [hI]; exact mem_univ _
  obtain ⟨j, hj, hje⟩ := Finset.mem_image.mp hq
  simp only [slice, mem_filter] at hj
  refine ⟨j, hj.1, ?_⟩
  funext x
  by_cases hxc : x.1 = c
  · have : x = ⟨c, hc⟩ := Subtype.ext hxc
    subst this
    simp [pat, hj.2, hp]
  · have := congrFun hje ⟨x.1, mem_erase.mpr ⟨hxc, x.2⟩⟩
    simpa [pat, patE] using this

/-- Some row of `F` leaves at most `k - 1` missing words on each side. -/
theorem exists_good_row (A : Table n m) (hA : DistinctColumns A) (F : Finset (Fin n))
    (S : Finset (Fin m)) (hS : AgreeOff A F S) (hS2 : 2 ≤ S.card)
    (hk : 2 ^ F.card ≤ S.card + F.card) :
    ∃ c ∈ F, ∀ b, 2 ^ (F.card - 1) ≤ (slice A S c b).card + (F.card - 1) := by
  classical
  have hle := card_le_two_pow A hA F S hS
  have hk1 : 1 ≤ F.card := by
    by_contra h0
    have : F.card = 0 := by omega
    rw [this] at hle; simp at hle; omega
  obtain ⟨t, ht⟩ : ∃ t, F.card = t + 1 := ⟨F.card - 1, by omega⟩
  have hpow : 2 ^ F.card = 2 * 2 ^ t := by rw [ht]; ring
  rw [ht, Nat.add_sub_cancel]
  have hsl : ∀ c ∈ F, ∀ b, (slice A S c b).card ≤ 2 ^ t := by
    intro c hc b
    have := slice_card_le A hA F S hS c hc b
    rwa [ht, Nat.add_sub_cancel] at this
  by_cases hcase : 2 ^ F.card ≤ S.card + t
  · obtain ⟨c, hc⟩ : F.Nonempty := Finset.card_pos.mp (by omega)
    refine ⟨c, hc, fun b => ?_⟩
    have hadd := slice_card_add A S c
    have h1 := hsl c hc true
    have h2 := hsl c hc false
    cases b <;> omega
  · -- exactly `k` missing words: they cannot all lie on one side of every row
    by_contra hno
    push_neg at hno
    -- for each `c ∈ F` some side is full
    have hfull : ∀ c (hc : c ∈ F), ∃ b, (slice A S c b).card = 2 ^ t ∧
        ∀ p : F → Bool, p ⟨c, hc⟩ = b → ∃ j ∈ S, pat A F j = p := by
      intro c hc
      obtain ⟨b, hb⟩ := hno c hc
      have hadd := slice_card_add A S c
      have h1 := hsl c hc true
      have h2 := hsl c hc false
      have hfb : (slice A S c (!b)).card = 2 ^ t := by cases b <;> simp at hb ⊢ <;> omega
      refine ⟨!b, hfb, fun p hp => ?_⟩
      exact full_slice_hits A hA F S hS c hc (!b) (by rw [hfb, ht, Nat.add_sub_cancel]) p hp
    -- two distinct missing patterns
    let Q := (univ : Finset (F → Bool)) \ S.image (pat A F)
    have hQ : 2 ≤ Q.card := by
      have hsub : S.image (pat A F) ⊆ univ := subset_univ _
      have hu : (univ : Finset (F → Bool)).card = 2 ^ F.card := by
        rw [card_univ, Fintype.card_fun, Fintype.card_coe, Fintype.card_bool]
      rw [Finset.card_sdiff_of_subset hsub, Finset.card_image_of_injOn (pat_injOn A hA F S hS), hu]
      have ht0 : t ≠ 0 := by
        rintro rfl
        simp at hpow
        omega
      omega
    obtain ⟨p, hp, p', hp', hpp⟩ := Finset.one_lt_card.mp (by omega : 1 < Q.card)
    have hmiss : ∀ q ∈ Q, ∀ j ∈ S, pat A F j ≠ q := by
      intro q hq j hj he
      simp only [Q, mem_sdiff, mem_univ, true_and, mem_image, not_exists, not_and] at hq
      exact hq j hj he
    obtain ⟨x, hx⟩ : ∃ x, p x ≠ p' x := by
      by_contra h; push_neg at h; exact hpp (funext h)
    obtain ⟨b, -, hb⟩ := hfull x.1 x.2
    have hb' := fun q => hb q
    rcases Bool.eq_or_eq_not (p x) b with h | h
    · obtain ⟨j, hj, hje⟩ := hb p (by simpa using h)
      exact hmiss p hp j hj hje
    · have : p' x = b := by
        cases hpx : p x <;> cases hp'x : p' x <;> cases b <;> simp_all
      obtain ⟨j, hj, hje⟩ := hb p' (by simpa using this)
      exact hmiss p' hp' j hj hje

/-- The core of Proposition 3.4: at most `k` missing words in a `k`-dimensional subcube. -/
theorem totalDepth_dense (A : Table n m) (hA : DistinctColumns A) (hn : 0 < n) :
    ∀ k, ∀ (F : Finset (Fin n)) (S : Finset (Fin m)), F.card = k → AgreeOff A F S →
      2 ^ k ≤ S.card + k → totalDepth A hn S = cdepth S.card := by
  intro k
  induction k with
  | zero =>
    intro F S hF hS _
    have := card_le_two_pow A hA F S hS
    rw [hF] at this
    rw [totalDepth_le_one A hn S (by simpa using this)]
    interval_cases h : S.card <;> simp [cdepth]
  | succ k ih =>
    intro F S hF hS hk
    by_cases hS2 : S.card ≤ 1
    · rw [totalDepth_le_one A hn S hS2]
      interval_cases h : S.card <;> simp [cdepth]
    push_neg at hS2
    have hS2' : 2 ≤ S.card := hS2
    set g := greedyRow A S hn with hg
    obtain ⟨j, hj⟩ : S.Nonempty := Finset.card_pos.mp (by omega)
    -- the greedy row lies in `F`
    have hgF : g ∈ F := by
      by_contra hgF
      obtain ⟨k', hk', hd⟩ := p1_opposite_of_quality_pos A S g j
        (p1_greedy_quality_pos A hA S j hn hj hS2')
      exact hd (hS k' hk' j hj g hgF)
    -- both children of the greedy row have at most `k` missing words
    obtain ⟨c, hcF, hc⟩ := exists_good_row A hA F S hS hS2' (by rwa [hF])
    rw [hF, Nat.add_sub_cancel] at hc
    have hqc : 2 ^ k ≤ quality A S c + k := by
      have h1 := hc true; have h0 := hc false
      simp only [slice] at h1 h0
      unfold quality ones zeros
      omega
    have hqg := p1_greedy_quality_max A S hn c
    have hchild : ∀ b, 2 ^ k ≤ (child A hn S b).card + k ∧ (child A hn S b).card ≤ 2 ^ k := by
      intro b
      have hup := slice_card_le A hA F S hS g hgF b
      rw [hF, Nat.add_sub_cancel] at hup
      refine ⟨?_, by simpa [slice, child, ← hg] using hup⟩
      have : quality A S g ≤ (child A hn S b).card := by
        unfold quality ones zeros child
        cases b
        · exact min_le_right _ _
        · exact min_le_left _ _
      rw [← hg] at hqg
      exact le_trans hqc (Nat.add_le_add_right (le_trans hqg this) k)
    have hagree : ∀ b, AgreeOff A (F.erase g) (child A hn S b) := by
      intro b j1 h1 j2 h2 r hr
      simp only [child, mem_filter, ← hg] at h1 h2
      by_cases hrg : r = g
      · subst hrg; rw [h1.2, h2.2]
      · exact hS j1 h1.1 j2 h2.1 r (fun hrF => hr (mem_erase.mpr ⟨hrg, hrF⟩))
    have hFe : (F.erase g).card = k := by rw [card_erase_of_mem hgF, hF, Nat.add_sub_cancel]
    have d1 := ih (F.erase g) (child A hn S true) hFe (hagree true) (hchild true).1
    have d0 := ih (F.erase g) (child A hn S false) hFe (hagree false) (hchild false).1
    rw [totalDepth_fork A hA hn S hS2', d1, d0]
    rw [← child_card_add A hn S]
    -- the two children lie in one dyadic interval
    have ht := hchild true; have hf := hchild false
    rcases Nat.eq_zero_or_pos k with hk0 | hkpos
    · subst hk0
      have e1 : (child A hn S true).card = 1 := by
        obtain ⟨a1, a2⟩ := ht; simp only [pow_zero, add_zero] at a1 a2; omega
      have e0 : (child A hn S false).card = 1 := by
        obtain ⟨a1, a2⟩ := hf; simp only [pow_zero, add_zero] at a1 a2; omega
      rw [e1, e0]; decide
    · have hkk := le_two_pow_pred k hkpos
      have hpk : 2 ^ k = 2 * 2 ^ (k - 1) := by
        rw [← pow_succ']; congr 1; omega
      have := cdepth_add (k - 1) (child A hn S true).card (child A hn S false).card
        (by omega) (by rw [Nat.sub_add_cancel hkpos]; omega)
        (by omega) (by rw [Nat.sub_add_cancel hkpos]; omega)
      omega

/-- **Proposition 3.4.** If `n ≥ 1` and `2^n - n ≤ m ≤ 2^n`, every table has cost `C(m)`. -/
theorem prop_dense_cost (hn : 0 < n) (hlow : 2 ^ n ≤ m + n) (A : Table n m)
    (hA : DistinctColumns A) : cost A hn = completeCost m := by
  have hm : 0 < m := by
    rcases Nat.eq_zero_or_pos m with h | h
    · subst h
      have := Nat.lt_two_pow_self (n := n); omega
    · exact h
  have hsum : ∑ j : Fin m, leafDepth A hn j = cdepth m := by
    rw [sum_leafDepth_eq_totalDepth A hA hn]
    have := totalDepth_dense A hA hn n univ univ (by simp) (fun _ _ _ _ r hr => absurd (mem_univ r) hr)
      (by simpa using hlow)
    simpa using this
  unfold cost completeCost
  rw [← Nat.cast_sum, hsum]
  unfold cdepth
  have hl : 2 ^ Nat.log 2 m ≤ m := Nat.pow_log_le_self 2 (by omega)
  have hle : 2 ^ (Nat.log 2 m + 1) ≤ m * (Nat.log 2 m + 2) := by
    calc 2 ^ (Nat.log 2 m + 1) = 2 * 2 ^ Nat.log 2 m := by ring
      _ ≤ 2 * m := by omega
      _ ≤ m * (Nat.log 2 m + 2) := by nlinarith
  rw [Nat.cast_sub hle]
  have hm' : (m : ℝ) ≠ 0 := by exact_mod_cast hm.ne'
  push_cast
  field_simp

/-- **Proposition 3.4**, average form: `t_{n,m}(G) = C(m)`. -/
theorem prop_dense (hn : 0 < n) (hlow : 2 ^ n ≤ m + n) (hsize : m ≤ 2 ^ n) (hm : 2 ≤ m) :
    tG n m hn = completeCost m := by
  have hne : Nonempty (Sample n m) := sample_nonempty hm hsize
  have hpos : 0 < Fintype.card (ValidTable n m) :=
    Fintype.card_pos_iff.mpr ⟨(Classical.arbitrary (Sample n m)).1⟩
  unfold tG
  rw [Finset.sum_congr rfl (fun A _ => prop_dense_cost hn hlow A.1 A.2), Finset.sum_const,
    Finset.card_univ, nsmul_eq_mul]
  have : (Fintype.card (ValidTable n m) : ℝ) ≠ 0 := by exact_mod_cast hpos.ne'
  field_simp

end GradientKey.Concrete
