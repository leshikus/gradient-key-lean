import NearTwoTop

/-!
# The sets of `n + 2` missing words with excess `1`

Such a set is `φ(j, b, c, Y)`: the ball of radius `1` around `c` on the rows `≠ j`, with bit `!b` in row `j`,
together with two words `Y` with bit `b` in row `j` such that row `j` is the first row of largest `μ`.
-/

noncomputable section

namespace GradientKey.Concrete

open Finset

variable {n : ℕ}

/-- The bit of `c` (a word on the rows `≠ j`) in row `i`; `false` at `i = j`. -/
def cbit (j : Fin n) (c : ((univ : Finset (Fin n)).erase j) → Bool) (i : Fin n) : Bool :=
  if h : i = j then false else c ⟨i, mem_erase.mpr ⟨h, mem_univ i⟩⟩

/-- The ball around `c` on the rows `≠ j`, with bit `!b` in row `j`. -/
def Bset (j : Fin n) (b : Bool) (c : ((univ : Finset (Fin n)).erase j) → Bool) : Finset (Word n) :=
  (ball c).image (fun q => extB univ j q (!b))

/-- The number of words of `Y` with bit `≠ ci` in row `i`. -/
def dev (Y : Finset (Word n)) (i : Fin n) (ci : Bool) : ℕ := (Y.filter (fun w => wbit w i ≠ ci)).card

/-- Row `j` is the first row of largest `μ`: no word of `Y` deviates from `c` before `j`, at most one after. -/
def CondY (j : Fin n) (c : ((univ : Finset (Fin n)).erase j) → Bool) (Y : Finset (Word n)) : Prop :=
  (∀ i, i < j → dev Y i (cbit j c i) = 0) ∧ (∀ i, j < i → dev Y i (cbit j c i) ≤ 1)

open Classical in
/-- The admissible pairs `Y`. -/
def Yset (j : Fin n) (b : Bool) (c : ((univ : Finset (Fin n)).erase j) → Bool) : Finset (Finset (Word n)) :=
  (powersetCard 2 univ).filter (fun Y => (∀ y ∈ Y, wbit y j = b) ∧ CondY j c Y)

theorem wbit_extB_self (j : Fin n) (q : ((univ : Finset (Fin n)).erase j) → Bool) (b : Bool) :
    wbit (extB univ j q b) j = b := by simp [wbit, extB]

theorem wbit_extB_ne (j : Fin n) (q : ((univ : Finset (Fin n)).erase j) → Bool) (b : Bool) {i : Fin n}
    (h : i ≠ j) : wbit (extB univ j q b) i = q ⟨i, mem_erase.mpr ⟨h, mem_univ i⟩⟩ := by
  simp [wbit, extB, h]

theorem extB_injective (j : Fin n) (b : Bool) :
    Function.Injective (fun q : ((univ : Finset (Fin n)).erase j) → Bool => extB univ j q b) := by
  intro q q' h
  funext y
  have hy : y.1 ≠ j := (mem_erase.mp y.2).1
  have := congrArg (fun w => wbit w y.1) h
  simp only [wbit_extB_ne j _ b hy] at this
  exact this

theorem card_Bset (hn : 1 ≤ n) (j : Fin n) (b : Bool) (c : ((univ : Finset (Fin n)).erase j) → Bool) :
    (Bset j b c).card = n := by
  unfold Bset
  rw [card_image_of_injective _ (extB_injective j (!b)), card_ball, Fintype.card_coe,
    card_erase_of_mem (mem_univ j), card_univ, Fintype.card_fin]
  omega

theorem wbit_Bset (j : Fin n) (b : Bool) (c : ((univ : Finset (Fin n)).erase j) → Bool) :
    ∀ w ∈ Bset j b c, wbit w j = !b := by
  intro w hw
  obtain ⟨q, -, rfl⟩ := mem_image.mp hw
  exact wbit_extB_self j q _

/-- In row `i ≠ j`, exactly one word of `Bset` has a bit `≠ c_i`. -/
theorem dev_Bset (j : Fin n) (b : Bool) (c : ((univ : Finset (Fin n)).erase j) → Bool) {i : Fin n}
    (hij : i ≠ j) : dev (Bset j b c) i (cbit j c i) = 1 := by
  unfold dev Bset
  set x : ((univ : Finset (Fin n)).erase j) := ⟨i, mem_erase.mpr ⟨hij, mem_univ i⟩⟩
  have hc : cbit j c i = c x := by simp [cbit, hij, x]
  rw [hc, filter_image]
  have : (ball c).filter (fun a => wbit (extB univ j a (!b)) i ≠ c x) =
      (ball c).filter (fun p => p x = !c x) := by
    congr 1; funext q
    simp only [wbit_extB_ne j q _ hij]
    cases q x <;> cases c x <;> simp
  rw [this, ball_filter_flip, image_singleton, card_singleton]

/-- `φ(j, b, c, Y)`. -/
def phiR (j : Fin n) (b : Bool) (c : ((univ : Finset (Fin n)).erase j) → Bool) (Y : Finset (Word n)) :
    Finset (Word n) := Bset j b c ∪ Y

section Phi

variable (j : Fin n) (b : Bool) (c : ((univ : Finset (Fin n)).erase j) → Bool) (Y : Finset (Word n))

theorem disjoint_Bset (hY : ∀ y ∈ Y, wbit y j = b) : Disjoint (Bset j b c) Y := by
  rw [disjoint_left]
  intro w hw hwY
  have h1 := wbit_Bset j b c w hw
  rw [hY w hwY] at h1
  cases b <;> simp at h1

theorem phi_filter_b (hY : ∀ y ∈ Y, wbit y j = b) :
    (phiR j b c Y).filter (fun w => wbit w j = b) = Y := by
  ext w
  simp only [phiR, mem_filter, mem_union]
  constructor
  · rintro ⟨hw | hw, hb⟩
    · have := wbit_Bset j b c w hw; rw [hb] at this; cases b <;> simp at this
    · exact hw
  · intro hw; exact ⟨Or.inr hw, hY w hw⟩

theorem phi_filter_nb (hY : ∀ y ∈ Y, wbit y j = b) :
    (phiR j b c Y).filter (fun w => wbit w j = !b) = Bset j b c := by
  ext w
  simp only [phiR, mem_filter, mem_union]
  constructor
  · rintro ⟨hw | hw, hb⟩
    · exact hw
    · have := hY w hw; rw [hb] at this; cases b <;> simp at this
  · intro hw; exact ⟨Or.inl hw, wbit_Bset j b c w hw⟩

theorem card_phi (hn : 1 ≤ n) (hY : ∀ y ∈ Y, wbit y j = b) (hY2 : Y.card = 2) :
    (phiR j b c Y).card = n + 2 := by
  unfold phiR
  rw [card_union_of_disjoint (disjoint_Bset j b c Y hY), card_Bset hn, hY2]

theorem dev_phi (hY : ∀ y ∈ Y, wbit y j = b) {i : Fin n} (hij : i ≠ j) (ci : Bool) :
    dev (phiR j b c Y) i ci = dev (Bset j b c) i ci + dev Y i ci := by
  unfold dev phiR
  rw [filter_union, card_union_of_disjoint]
  exact disjoint_filter_filter (disjoint_Bset j b c Y hY)

theorem muR_phi_j (hn4 : 4 ≤ n) (hY : ∀ y ∈ Y, wbit y j = b) (hY2 : Y.card = 2) :
    muR (phiR j b c Y) j = 2 := by
  unfold muR
  cases b
  · have h1 := phi_filter_b j false c Y hY
    have h0 := phi_filter_nb j false c Y hY
    simp only [Bool.not_false] at h0
    rw [h1, h0, hY2, card_Bset (by omega)]; omega
  · have h1 := phi_filter_b j true c Y hY
    have h0 := phi_filter_nb j true c Y hY
    simp only [Bool.not_true] at h0
    rw [h1, h0, hY2, card_Bset (by omega)]; omega

theorem dev_false (X : Finset (Word n)) (i : Fin n) :
    dev X i false = (X.filter (fun w => wbit w i = true)).card := by
  unfold dev; congr 1; ext w; cases wbit w i <;> simp

theorem dev_true (X : Finset (Word n)) (i : Fin n) :
    dev X i true = (X.filter (fun w => wbit w i = false)).card := by
  unfold dev; congr 1

theorem filter_true_add_false (X : Finset (Word n)) (i : Fin n) :
    (X.filter (fun w => wbit w i = true)).card + (X.filter (fun w => wbit w i = false)).card = X.card := by
  have := card_filter_add_card_filter_not (s := X) (fun w => wbit w i = true)
  simpa using this

theorem muR_phi_ne (hn4 : 4 ≤ n) (hY : ∀ y ∈ Y, wbit y j = b) (hY2 : Y.card = 2) {i : Fin n}
    (hij : i ≠ j) : muR (phiR j b c Y) i = 1 + dev Y i (cbit j c i) := by
  have hd := dev_phi j b c Y hY hij (cbit j c i)
  rw [dev_Bset j b c hij] at hd
  have htot := card_phi j b c Y (by omega) hY hY2
  have hsplit := filter_true_add_false (phiR j b c Y) i
  have hdY : dev Y i (cbit j c i) ≤ 2 := by unfold dev; rw [← hY2]; exact card_filter_le _ _
  unfold muR
  generalize cbit j c i = ci at hd hdY ⊢
  cases ci
  · simp only [dev_false] at hd hdY ⊢; omega
  · simp only [dev_true] at hd hdY ⊢; omega

theorem gR_phi_iff (hn : 0 < n) (hn4 : 4 ≤ n) (hY : ∀ y ∈ Y, wbit y j = b) (hY2 : Y.card = 2) :
    gR (phiR j b c Y) hn = j ↔ CondY j c Y := by
  unfold gR
  rw [first_argmax_iff, muR_phi_j j b c Y hn4 hY hY2]
  unfold CondY
  constructor
  · rintro ⟨h1, h2⟩
    refine ⟨fun i hi => ?_, fun i hi => ?_⟩
    · have := h2 i hi; rw [muR_phi_ne j b c Y hn4 hY hY2 (ne_of_lt hi)] at this; omega
    · have := h1 i; rw [muR_phi_ne j b c Y hn4 hY hY2 (ne_of_gt hi)] at this; omega
  · rintro ⟨h1, h2⟩
    refine ⟨fun i => ?_, fun i hi => ?_⟩
    · rcases lt_trichotomy i j with h | h | h
      · rw [muR_phi_ne j b c Y hn4 hY hY2 (ne_of_lt h), h1 i h]; omega
      · rw [h, muR_phi_j j b c Y hn4 hY hY2]
      · rw [muR_phi_ne j b c Y hn4 hY hY2 (ne_of_gt h)]; have := h2 i h; omega
    · rw [muR_phi_ne j b c Y hn4 hY hY2 (ne_of_lt hi), h1 i hi]; omega

end Phi

open Classical in
theorem mem_Yset {j : Fin n} {b : Bool} {c : ((univ : Finset (Fin n)).erase j) → Bool}
    {Y : Finset (Word n)} : Y ∈ Yset j b c ↔ Y.card = 2 ∧ (∀ y ∈ Y, wbit y j = b) ∧ CondY j c Y := by
  unfold Yset
  simp [mem_powersetCard]

theorem QR_phi (hn : 0 < n) (hn4 : 4 ≤ n) (j : Fin n) (b : Bool)
    (c : ((univ : Finset (Fin n)).erase j) → Bool) (Y : Finset (Word n)) (hY : Y ∈ Yset j b c) :
    QR (phiR j b c Y) hn := by
  obtain ⟨hY2, hYb, hC⟩ := mem_Yset.mp hY
  have hg := (gR_phi_iff j b c Y hn hn4 hYb hY2).mpr hC
  unfold QR
  rw [hg]
  refine ⟨b, by rw [phi_filter_b j b c Y hYb, hY2], c, ?_⟩
  ext q
  simp only [mem_filter, mem_univ, true_and, phiR, mem_union]
  constructor
  · rintro (h | h)
    · obtain ⟨q', hq', he⟩ := mem_image.mp h
      rw [← extB_injective j (!b) he]; exact hq'
    · have := hYb _ h; rw [wbit_extB_self] at this; cases b <;> simp at this
  · intro h; exact Or.inl (mem_image_of_mem _ h)

/-- Every set with excess `1` is some `φ(j, b, c, Y)`. -/
theorem phi_of_QR (hn : 0 < n) (hn4 : 4 ≤ n) (R : Finset (Word n)) (_hR : R.card = n + 2)
    (hQ : QR R hn) : ∃ b c, R = phiR (gR R hn) b c (R.filter (fun w => wbit w (gR R hn) = b)) ∧
      R.filter (fun w => wbit w (gR R hn) = b) ∈ Yset (gR R hn) b c := by
  obtain ⟨b, hb, c, hc⟩ := hQ
  have hYb : ∀ y ∈ R.filter (fun w => wbit w (gR R hn) = b), wbit y (gR R hn) = b :=
    fun y hy => (mem_filter.mp hy).2
  have hB : R.filter (fun w => wbit w (gR R hn) = !b) = Bset (gR R hn) b c := by
    ext w
    simp only [mem_filter, Bset, mem_image]
    constructor
    · rintro ⟨hw, hwb⟩
      have he := (extB_eq_iff univ (gR R hn) (mem_univ _) (resW univ (gR R hn) w) (!b) w).mpr ⟨hwb, rfl⟩
      refine ⟨resW univ (gR R hn) w, ?_, he⟩
      rw [← hc, mem_filter]
      exact ⟨mem_univ _, by rw [he]; exact hw⟩
    · rintro ⟨q, hq, rfl⟩
      rw [← hc, mem_filter] at hq
      exact ⟨hq.2, wbit_extB_self _ q _⟩
  have hRphi : R = phiR (gR R hn) b c (R.filter (fun w => wbit w (gR R hn) = b)) := by
    rw [phiR, ← hB]
    ext w
    simp only [mem_union, mem_filter]
    constructor
    · intro hw
      cases h : wbit w (gR R hn) <;> cases b <;> simp_all
    · rintro (⟨hw, -⟩ | ⟨hw, -⟩) <;> exact hw
  refine ⟨b, c, hRphi, mem_Yset.mpr ⟨hb, hYb, ?_⟩⟩
  rw [← gR_phi_iff (gR R hn) b c _ hn hn4 hYb hb, ← hRphi]

/-- `φ` determines its parameters. -/
theorem phi_inj (hn : 0 < n) (hn4 : 4 ≤ n) {j j' : Fin n} {b b' : Bool}
    {c : ((univ : Finset (Fin n)).erase j) → Bool} {c' : ((univ : Finset (Fin n)).erase j') → Bool}
    {Y Y' : Finset (Word n)} (hY : Y ∈ Yset j b c) (hY' : Y' ∈ Yset j' b' c')
    (h : phiR j b c Y = phiR j' b' c' Y') : j = j' ∧ b = b' ∧ HEq c c' ∧ Y = Y' := by
  obtain ⟨hY2, hYb, hC⟩ := mem_Yset.mp hY
  obtain ⟨hY2', hYb', hC'⟩ := mem_Yset.mp hY'
  have hj : j = j' := by
    rw [← (gR_phi_iff j b c Y hn hn4 hYb hY2).mpr hC, ← (gR_phi_iff j' b' c' Y' hn hn4 hYb' hY2').mpr hC', h]
  subst hj
  have hb : b = b' := by
    by_contra hne
    have hb' : b' = !b := by cases b <;> cases b' <;> simp_all
    subst hb'
    have e1 := phi_filter_b j b c Y hYb
    rw [h] at e1
    have e2 := phi_filter_nb j (!b) c' Y' hYb'
    simp only [Bool.not_not] at e2
    rw [e2] at e1
    have := congrArg Finset.card e1
    rw [card_Bset (by omega), hY2] at this
    omega
  subst hb
  have hYY : Y = Y' := by
    rw [← phi_filter_b j b c Y hYb, ← phi_filter_b j b c' Y' hYb', h]
  subst hYY
  have hBB : Bset j b c = Bset j b c' := by
    rw [← phi_filter_nb j b c Y hYb, ← phi_filter_nb j b c' Y hYb', h]
  have hball : ball c = ball c' := image_injective (extB_injective j (!b)) hBB
  have hcc : c = c' := ball_injective (by
    rw [Fintype.card_coe, card_erase_of_mem (mem_univ j), card_univ, Fintype.card_fin]; omega) hball
  exact ⟨rfl, rfl, heq_of_eq hcc, rfl⟩

end GradientKey.Concrete
