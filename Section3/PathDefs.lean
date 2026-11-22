import PathMobius

/-!
# Proposition 3.1: finite version of the exact path formula

Integer partitions are represented by their multiplicity vectors: a part
of size `v` occurs `multiplicity v` times. This is equivalent to the
article's list-of-parts notation, and gives finite index types directly.
The coefficient `c`, assignment counts `W` and `V`, injection sum `F`,
chain weight, and complete RHS are all defined from these data.

IMPORTANT: uncompiled draft for Lean v4.36.0 / Mathlib v4.36.0.
No proof of equivalence with `Nat.Partition` or the actual `tG` is
included. No declarations have been pushed to GitHub.
-/

noncomputable section

namespace GradientKey.Concrete

open Finset Classical

/-- Strictly decreasing candidate sizes, encoded as bounded natural numbers. -/
abbrev PathSizeVector (m d : ℕ) := Fin (d + 1) → Fin (m + 1)

/-- A path is indexed by `d < n` and sizes `m=s₀>...>s_d≥2`. -/
def IsPathChain (m d : ℕ) (s : PathSizeVector m d) : Prop :=
  (s ⟨0, Nat.zero_lt_succ d⟩).val = m ∧
  2 ≤ (s (Fin.last d)).val ∧
  ∀ j : Fin d, (s (Fin.succ j)).val < (s (Fin.castSucc j)).val

/-- Exactly the article's finite collection `𝒞_{m,n}`. -/
abbrev PathChain (n m : ℕ) :=
  { x : (d : Fin n) × PathSizeVector m d.val // IsPathChain m x.1.val x.2 }

/-- Length of a chain, i.e. the depth of its last fork. -/
def pathChainDepth {n m : ℕ} (s : PathChain n m) : ℕ := s.1.1.val

/-- Candidate set sizes along a chain. -/
def pathChainSizes {n m : ℕ} (s : PathChain n m) :
    PathSizeVector m (pathChainDepth s) := s.1.2

/-- Size of the `j`-th cell: `a_j=s_j-s_{j+1}` if `j<d`, `a_d=s_d`. -/
def pathCellSize {n m : ℕ} (s : PathChain n m)
    (j : Fin (pathChainDepth s + 1)) : ℕ :=
  if h : j.val < pathChainDepth s then
    (pathChainSizes s j).val -
      (pathChainSizes s ⟨j.val + 1, by omega⟩).val
  else (pathChainSizes s j).val

/-- Greedy quality for the `j`-th fork: `min(a_j,s_{j+1})`. -/
def pathQuality {n m : ℕ} (s : PathChain n m)
    (j : Fin (pathChainDepth s)) : ℕ :=
  min (pathCellSize s (Fin.castSucc j))
      (pathChainSizes s (Fin.succ j)).val

/-- The multiplicity vector of an integer partition of `a`.
    Parts of size 0 cannot occur; no part can be larger than `m`. -/
abbrev PathPartition (m a : ℕ) :=
  { u : Fin (m + 1) → Fin (m + 1) //
      (u ⟨0, Nat.zero_lt_succ m⟩).val = 0 ∧
      (∑ v : Fin (m + 1), v.val * (u v).val) = a }

/-- Number of blocks in a partition type. -/
def pathPartCount {m a : ℕ} (part : PathPartition m a) : ℕ :=
  ∑ v : Fin (m + 1), (part.1 v).val

/-- Exact rational form of the article's Möbius coefficient
    `(-1)^(a-p) a! / (∏ v^(multiplicity v) multiplicity(v)!)`. -/
def pathCoeff {m a : ℕ} (part : PathPartition m a) : ℚ :=
  ((-1 : ℚ) ^ (a - pathPartCount part) * (a.factorial : ℚ)) /
    (∏ v : Fin (m + 1),
      (v.val : ℚ) ^ (part.1 v).val *
        (((part.1 v).val.factorial : ℕ) : ℚ))

/-- Assign one integer partition to each cell. -/
abbrev PathPartitionTypes {n m : ℕ} (s : PathChain n m) :=
  (j : Fin (pathChainDepth s + 1)) → PathPartition m (pathCellSize s j)

/-- Each actual block has a cell index `j` and a part-size index `v`. -/
abbrev PathBlocks {n m : ℕ} (s : PathChain n m)
    (parts : PathPartitionTypes s) :=
  (j : Fin (pathChainDepth s + 1)) ×
    ((v : Fin (m + 1)) × Fin ((parts j).1 v).val)

/-- A row constant on blocks is encoded by one bit per block. -/
abbrev PathAssignment {n m : ℕ} (s : PathChain n m)
    (parts : PathPartitionTypes s) := PathBlocks s parts → Bool

/-- Weighted number of ones in the suffix `S_i`, i.e. cells `i..d`. -/
def pathOnes {n m : ℕ} (s : PathChain n m)
    (parts : PathPartitionTypes s) (bits : PathAssignment s parts)
    (i : Fin (pathChainDepth s + 1)) : ℕ :=
  ∑ block : PathBlocks s parts,
    if i.val ≤ block.1.val ∧ bits block = true then block.2.1.val else 0

/-- Quality of a block-constant row restricted to `S_i`. -/
def pathRowQuality {n m : ℕ} (s : PathChain n m)
    (parts : PathPartitionTypes s) (bits : PathAssignment s parts)
    (i : Fin (pathChainDepth s + 1)) : ℕ :=
  min (pathOnes s parts bits i)
    ((pathChainSizes s i).val - pathOnes s parts bits i)

/-- The row-quality requirements at a particular earlier fork. -/
def pathMeetsQuality {n m : ℕ} (s : PathChain n m)
    (parts : PathPartitionTypes s) (bits : PathAssignment s parts)
    (M : Finset (Fin (pathChainDepth s)))
    (j : Fin (pathChainDepth s)) : Prop :=
  if j ∈ M then
    pathRowQuality s parts bits (Fin.castSucc j) ≤ pathQuality s j
  else
    pathRowQuality s parts bits (Fin.castSucc j) < pathQuality s j

/-- `W(M)`: all block assignments satisfying every row-quality bound. -/
def pathW {n m : ℕ} (s : PathChain n m)
    (parts : PathPartitionTypes s)
    (M : Finset (Fin (pathChainDepth s))) : ℕ :=
  (univ.filter (fun bits : PathAssignment s parts =>
    ∀ j : Fin (pathChainDepth s), pathMeetsQuality s parts bits M j)).card

/-- `V_j(M)`: block assignments with opposite constant bits in cell `j`
    and in its suffix `S_(j+1)`, satisfying earlier quality tests. -/
def pathV {n m : ℕ} (s : PathChain n m)
    (parts : PathPartitionTypes s)
    (j : Fin (pathChainDepth s))
    (M : Finset (Fin (pathChainDepth s))) : ℕ :=
  (univ.filter (fun bits : PathAssignment s parts =>
    (∃ b : Bool,
      (∀ block : PathBlocks s parts,
        (block.1.val = j.val → bits block = !b) ∧
        (j.val < block.1.val → bits block = b))) ∧
    (∀ i : Fin (pathChainDepth s), i.val < j.val →
        pathMeetsQuality s parts bits M i))).card

/-- All fork indices whose selected row precedes `r`. -/
def pathBefore {n m : ℕ} (s : PathChain n m)
    (rho : Fin (pathChainDepth s) ↪ Fin n) (r : Fin n) :
    Finset (Fin (pathChainDepth s)) :=
  univ.filter (fun j => rho j < r)

/-- The `F_n` of Proposition 3.1, summed over all injective row schedules. -/
def pathF {n m : ℕ} (s : PathChain n m)
    (parts : PathPartitionTypes s) : ℕ :=
  ∑ rho : Fin (pathChainDepth s) ↪ Fin n,
    (∏ r ∈ (univ.filter (fun r : Fin n =>
        ∀ j : Fin (pathChainDepth s), rho j ≠ r)),
      pathW s parts (pathBefore s rho r)) *
    (∏ j : Fin (pathChainDepth s),
      pathV s parts j (pathBefore s rho (rho j)))

/-- Number of nested set families of the given sizes, per fixed column. -/
def pathFamilyFactor {n m : ℕ} (s : PathChain n m) : ℕ :=
  ∏ j : Fin (pathChainDepth s),
    Nat.choose ((pathChainSizes s (Fin.castSucc j)).val - 1)
      ((pathChainSizes s (Fin.succ j)).val - 1)

/-- Exact chain contribution: binomial factor times Möbius-partition sum. -/
def pathChainTerm {n m : ℕ} (s : PathChain n m) : ℚ :=
  (pathFamilyFactor s : ℚ) *
    (∑ parts : PathPartitionTypes s,
      (∏ j : Fin (pathChainDepth s + 1),
        pathCoeff (parts j)) * (pathF s parts : ℚ))

/-- The full right-hand side of Proposition 3.1, as a real number. -/
def pathFormulaRHS (n m : ℕ) : ℝ :=
  (∑ s : PathChain n m, (pathChainTerm s : ℝ)) /
    (((2 ^ n).descFactorial m : ℕ) : ℝ)

end GradientKey.Concrete
