import NearTwo
import Counting
import Optimal

/-!
# Proposition 3.5, second formula: the root in terms of the missing words

For a table `A ∈ 𝒜_{n,m}` with `n ≥ 4` and `m = 2^n - n - 2`, let `R` be its `n + 2` missing words. The greedy row
at the root is the first row `i` of largest `μ_R(i) = min(#{w ∈ R : w_i = 1}, #{w ∈ R : w_i = 0})`, and the
condition `TwoBall` of `near_two` depends only on `R`.
-/

noncomputable section


namespace GradientKey.Concrete

open Finset

variable {n m : ℕ}

/-- Bit `i` of a word. -/
def wbit (w : Word n) (i : Fin n) : Bool := w ⟨i, mem_univ i⟩

/-- `μ_R(i)`: the smaller number of words of `R` on a side of row `i`. -/
def muR (R : Finset (Word n)) (i : Fin n) : ℕ :=
  min (R.filter (fun w => wbit w i = true)).card (R.filter (fun w => wbit w i = false)).card

/-- The first row of largest `μ_R`. -/
def gR (R : Finset (Word n)) (hn : 0 < n) : Fin n :=
  (List.argmax (muR R) (List.finRange n)).getD ⟨0, hn⟩

/-- The condition of excess `1`, in terms of the missing words. -/
def QR (R : Finset (Word n)) (hn : 0 < n) : Prop :=
  ∃ b, (R.filter (fun w => wbit w (gR R hn) = b)).card = 2 ∧
    ∃ c, univ.filter (fun q => extB univ (gR R hn) q (!b) ∈ R) = ball c

/-- The first maximizer of `f` on `Fin n`. -/
theorem first_argmax_iff (f : Fin n → ℕ) (hn : 0 < n) (j : Fin n) :
    (List.argmax f (List.finRange n)).getD ⟨0, hn⟩ = j ↔
      (∀ i, f i ≤ f j) ∧ (∀ i, i < j → f i < f j) := by
  have hne : List.finRange n ≠ [] := by
    intro he
    have : (⟨0, hn⟩ : Fin n) ∈ List.finRange n := List.mem_finRange _
    simp [he] at this
  obtain ⟨a, ha⟩ : ∃ a, List.argmax f (List.finRange n) = some a := by
    cases h : List.argmax f (List.finRange n) with
    | none => exact absurd (List.argmax_eq_none.mp h) hne
    | some a => exact ⟨a, rfl⟩
  have hmax : ∀ i, f i ≤ f a := fun i => List.le_of_mem_argmax (List.mem_finRange i) ha
  have hfirst : ∀ i, f a ≤ f i → a ≤ i := by
    intro i hi
    have := List.index_of_argmax ha hi
    simp only [List.idxOf_finRange] at this
    exact Fin.le_iff_val_le_val.mpr this
  rw [ha, Option.getD_some]
  constructor
  · rintro rfl
    refine ⟨hmax, fun i hi => ?_⟩
    by_contra h
    exact absurd (hfirst i (by omega)) (not_le.mpr hi)
  · rintro ⟨h1, h2⟩
    have e : f a = f j := le_antisymm (h1 a) (hmax j)
    rcases lt_or_eq_of_le (hfirst j e.le) with h | h
    · have := h2 a h; omega
    · exact h

/-- At the root, `quality(x) + (n + 2) = 2^{n-1} + μ_R(x)`. -/
theorem quality_root (A : Table n m) (hA : DistinctColumns A) (x : Fin n)
    (hR : (missing A univ univ).card = n + 2) :
    quality A univ x + (n + 2) = 2 ^ (n - 1) + muR (missing A univ univ) x := by
  have hS : AgreeOff A univ univ := fun _ _ _ _ r hr => absurd (mem_univ r) hr
  have h1 := slice_add_missing A hA univ univ hS x (mem_univ x) true
  have h0 := slice_add_missing A hA univ univ hS x (mem_univ x) false
  have hs := missing_filter_add A univ univ ⟨x, mem_univ x⟩
  rw [card_univ, Fintype.card_fin] at h1 h0
  rw [quality_eq]
  unfold muR
  have e1 : ((missing A univ univ).filter (fun w => wbit w x = true)).card =
      ((missing A univ univ).filter (fun p => p ⟨x, mem_univ x⟩ = true)).card := rfl
  have e0 : ((missing A univ univ).filter (fun w => wbit w x = false)).card =
      ((missing A univ univ).filter (fun p => p ⟨x, mem_univ x⟩ = false)).card := rfl
  rw [e1, e0]
  rw [hR] at hs
  omega

theorem greedyRow_root (A : Table n m) (hA : DistinctColumns A) (hn : 0 < n)
    (hR : (missing A univ univ).card = n + 2) :
    greedyRow A univ hn = gR (missing A univ univ) hn := by
  have hq := fun x => quality_root A hA x hR
  obtain ⟨h1, h2⟩ := (first_argmax_iff (muR (missing A univ univ)) hn (gR (missing A univ univ) hn)).mp rfl
  apply greedyRow_eq
  · intro r; have := h1 r; have := hq r; have := hq (gR (missing A univ univ) hn); omega
  · intro r hr; have := h2 r hr; have := hq r; have := hq (gR (missing A univ univ) hn); omega

theorem missing_slice_root (A : Table n m) (g : Fin n) (b : Bool) :
    missing A (univ.erase g) (slice A univ g b) =
      univ.filter (fun q => extB univ g q b ∈ missing A univ univ) := by
  ext q
  rw [mem_missing_slice A univ univ g (mem_univ g) b q]
  simp

/-- `TwoBall` at the root is `QR` of the missing words. -/
theorem twoBall_root (A : Table n m) (hA : DistinctColumns A) (hn : 0 < n) (_hn4 : 4 ≤ n)
    (hR : (missing A univ univ).card = n + 2) :
    TwoBall A hn univ univ n ↔ QR (missing A univ univ) hn := by
  have hS : AgreeOff A univ univ := fun _ _ _ _ r hr => absurd (mem_univ r) hr
  unfold TwoBall QR
  rw [greedyRow_root A hA hn hR]
  set g := gR (missing A univ univ) hn
  have hsm : ∀ b, (slice A univ g b).card + ((missing A univ univ).filter (fun w => wbit w g = b)).card =
      2 ^ (n - 1) := by
    intro b
    have := slice_add_missing A hA univ univ hS g (mem_univ g) b
    rwa [card_univ, Fintype.card_fin] at this
  simp only [missing_slice_root]
  constructor
  · rintro ⟨b, hb, c, hc⟩; exact ⟨b, by have := hsm b; omega, c, hc⟩
  · rintro ⟨b, hb, c, hc⟩; exact ⟨b, by have := hsm b; omega, c, hc⟩

end GradientKey.Concrete
