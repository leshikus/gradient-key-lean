import Optimal

/-!
# The greedy tree of a list of rows

`G` depends on a table only through its list of rows. This file defines the tree for any list `L` of rows,
shows that it is the tree of the table, and that it does not change when a row is complemented (`canon`) or when
a row equal to an earlier one is removed (`firsts`, the rows in order of first appearance).
-/

noncomputable section

namespace GradientKey.Concrete

open Finset

variable {n m : ℕ}

/-- A row: a binary pattern on the `m` columns. -/
abbrev Row (m : ℕ) := Fin m → Bool

/-- The quality `min(k, s-k)` of a row on `S`. -/
def rq (S : Finset (Fin m)) (r : Row m) : ℕ :=
  min (S.filter (fun k => r k = true)).card (S.filter (fun k => r k = false)).card

/-- One step on the path of `j` in the greedy tree of the row list `L`. -/
def lstep (L : List (Row m)) (S : Finset (Fin m)) (j : Fin m) : Finset (Fin m) :=
  if S.card ≤ 1 then S else
    match List.argmax (rq S) L with
    | none => S
    | some r => S.filter (fun k => r k = r j)

def lcand (L : List (Row m)) (j : Fin m) (i : ℕ) : Finset (Fin m) := (fun T => lstep L T j)^[i] univ

/-- Total depth `∑_j L_j` of the greedy tree of `L` (forks among the first `m` depths). -/
def ldepth (L : List (Row m)) : ℕ :=
  ∑ j : Fin m, ((range m).filter (fun i => 2 ≤ (lcand L j i).card)).card

theorem ldepth_of_lstep {L L' : List (Row m)} (hs : ∀ T j, lstep L T j = lstep L' T j) :
    ldepth L = ldepth L' := by
  have hc : ∀ j i, lcand L j i = lcand L' j i := by
    intro j i
    unfold lcand
    rw [show (fun T => lstep L T j) = (fun T => lstep L' T j) from funext (fun T => hs T j)]
  unfold ldepth
  simp only [hc]

theorem ldepth_congr {L L' : List (Row m)} (h : ∀ S, List.argmax (rq S) L = List.argmax (rq S) L') :
    ldepth L = ldepth L' :=
  ldepth_of_lstep (fun T j => by unfold lstep; rw [h T])

theorem argmax_map {α β γ : Type*} [LinearOrder β] (f : γ → β) (g : α → γ) :
    ∀ l : List α, List.argmax f (l.map g) = (List.argmax (f ∘ g) l).map g
  | [] => rfl
  | a :: t => by
    rw [List.map_cons, List.argmax_cons, List.argmax_cons, argmax_map f g t]
    cases List.argmax (f ∘ g) t with
    | none => rfl
    | some c => simp only [Option.map_some, Function.comp]; split_ifs <;> rfl

/-- The table's tree is the tree of its list of rows. -/
theorem candidateStep_eq_lstep (A : Table n m) (S : Finset (Fin m)) (j : Fin m) (hn : 0 < n) :
    candidateStep A S j hn = lstep (List.ofFn A) S j := by
  unfold candidateStep lstep
  split_ifs with h
  · rfl
  · rw [List.ofFn_eq_map, argmax_map]
    have : rq S ∘ A = quality A S := rfl
    rw [this, p1_argmax_some A S hn]
    rfl

theorem totalDepth_eq_ldepth (A : Table n m) (hn : 0 < n) :
    totalDepth A hn univ = ldepth (List.ofFn A) := by
  unfold totalDepth ldepth forksN
  rw [card_univ, Fintype.card_fin]
  apply sum_congr rfl
  intro j _
  congr 2
  funext i
  have : candFrom A hn univ j i = lcand (List.ofFn A) j i := by
    unfold candFrom lcand
    congr 1
    funext T
    exact candidateStep_eq_lstep A T j hn
  rw [this]

/-! ## Complementing rows -/

/-- The representative of a row up to complement with a `0` in column `0`. -/
def canon (hm : 0 < m) (r : Row m) : Row m := if r ⟨0, hm⟩ then fun k => !r k else r

theorem canon_zero (hm : 0 < m) (r : Row m) : canon hm r ⟨0, hm⟩ = false := by
  unfold canon; split_ifs with h <;> simp_all

theorem canon_eq_iff (hm : 0 < m) (r : Row m) (k j : Fin m) : canon hm r k = canon hm r j ↔ r k = r j := by
  unfold canon; split_ifs <;> simp

theorem canon_ne_iff (hm : 0 < m) (r : Row m) (k j : Fin m) : canon hm r k ≠ canon hm r j ↔ r k ≠ r j := by
  rw [Ne, Ne, canon_eq_iff]

theorem rq_canon (hm : 0 < m) (S : Finset (Fin m)) (r : Row m) : rq S (canon hm r) = rq S r := by
  unfold rq canon
  split_ifs
  · simp only [Bool.not_eq_true', Bool.not_eq_false']; rw [min_comm]
  · rfl

theorem ldepth_map_canon (hm : 0 < m) (L : List (Row m)) : ldepth (L.map (canon hm)) = ldepth L := by
  have hs : ∀ T j, lstep (L.map (canon hm)) T j = lstep L T j := by
    intro T j
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
  exact ldepth_of_lstep hs

/-! ## Rows in order of first appearance -/

section Firsts

variable {α : Type*} [DecidableEq α]

/-- The distinct entries of a list in order of first appearance. -/
def firsts (l : List α) : List α := l.foldl (fun acc a => if a ∈ acc then acc else acc ++ [a]) []

theorem firsts_nil : firsts ([] : List α) = [] := rfl

theorem firsts_concat (l : List α) (a : α) :
    firsts (l ++ [a]) = if a ∈ firsts l then firsts l else firsts l ++ [a] := by
  unfold firsts; rw [List.foldl_append]; rfl

theorem mem_firsts (l : List α) (a : α) : a ∈ firsts l ↔ a ∈ l := by
  induction l using List.reverseRecOn with
  | nil => simp [firsts_nil]
  | append_singleton l b ih =>
    rw [firsts_concat]
    split_ifs with h
    · rw [ih]; simp only [List.mem_append, List.mem_singleton]
      constructor
      · exact Or.inl
      · rintro (h' | rfl); exact h'; exact (ih).mp h
    · simp [ih]

theorem nodup_firsts (l : List α) : (firsts l).Nodup := by
  induction l using List.reverseRecOn with
  | nil => simp [firsts_nil]
  | append_singleton l b ih =>
    rw [firsts_concat]
    split_ifs with h
    · exact ih
    · refine List.nodup_append.mpr ⟨ih, List.nodup_singleton b, ?_⟩
      intro a ha c hc
      rw [List.mem_singleton] at hc
      subst hc
      exact fun e => h (e ▸ ha)

theorem argmax_firsts {β : Type*} [LinearOrder β] (f : α → β) (l : List α) :
    List.argmax f (firsts l) = List.argmax f l := by
  induction l using List.reverseRecOn with
  | nil => rfl
  | append_singleton l b ih =>
    rw [firsts_concat]
    split_ifs with h
    · rw [List.argmax_concat, ← ih]
      cases hc : List.argmax f (firsts l) with
      | none => exact absurd (List.argmax_eq_none.mp hc) (List.ne_nil_of_mem h)
      | some c =>
        have : ¬ f c < f b := not_lt.mpr (List.le_of_mem_argmax h hc)
        simp [this]
    · rw [List.argmax_concat, List.argmax_concat, ih]

theorem firsts_eq_self (l : List α) (h : l.Nodup) : firsts l = l := by
  induction l using List.reverseRecOn with
  | nil => rfl
  | append_singleton l b ih =>
    have hl := (List.nodup_append.mp h).1
    have hb : b ∉ l := by
      have := (List.nodup_append.mp h).2.2
      intro hb; exact this b hb b (List.mem_singleton_self b) rfl
    rw [firsts_concat, ih hl, if_neg hb]

end Firsts

theorem ldepth_firsts (L : List (Row m)) : ldepth (firsts L) = ldepth L :=
  ldepth_congr (fun S => argmax_firsts (rq S) L)

/-! ## Separation of the columns -/

/-- The rows of `L` separate the columns. -/
def Sep (L : List (Row m)) : Prop := ∀ j k : Fin m, j ≠ k → ∃ r ∈ L, r j ≠ r k

theorem sep_iff_distinct (A : Table n m) : Sep (List.ofFn A) ↔ DistinctColumns A := by
  constructor
  · intro h j k hjk
    by_contra hne
    obtain ⟨r, hr, hd⟩ := h j k hne
    obtain ⟨i, rfl⟩ := List.mem_ofFn.mp hr
    exact hd (congrFun hjk i)
  · intro h j k hjk
    by_contra hno
    push_neg at hno
    apply hjk
    apply h
    funext i
    exact hno (A i) (List.mem_ofFn.mpr ⟨i, rfl⟩)

theorem sep_map_canon (hm : 0 < m) (L : List (Row m)) : Sep (L.map (canon hm)) ↔ Sep L := by
  unfold Sep
  simp only [List.mem_map, exists_exists_and_eq_and, canon_ne_iff]

theorem sep_firsts [DecidableEq (Row m)] (L : List (Row m)) : Sep (firsts L) ↔ Sep L := by
  unfold Sep; simp only [mem_firsts]

end GradientKey.Concrete
