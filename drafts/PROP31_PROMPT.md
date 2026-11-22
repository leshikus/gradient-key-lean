# Formalize Proposition 3.1 (the path formula) in Lean 4

## Mission

Formalize Proposition 3.1 of *The gradient key on random tables* (`article.tex`, label `prop:path-formula`,
Section 3.1 "The path formula"): the exact formula for `t_{n,m}(G)` as a sum over chains, and the pruning
claim. Connect it to the existing `tG`. Implement, compile, verify, commit and push the proofs; do not stop
at a plan.

- Repository: https://github.com/leshikus/gradient-key-lean
- Branch: `section3` (verify the current HEAD; it was `140d441` when this prompt was written)
- Pull request: #1 (draft, open)
- Mathematical source: `article.tex`, Section 3.1 (quoted in §1 below)

Work autonomously, milestone by milestone. Push after every substantive update (rule 10), not only at milestones.

## 0. Rules (non-negotiable)

1. Work only on branch `section3` and PR #1. Do not modify, merge into or push to `main`. No new branches or PRs.
   Never force-push.
2. Keep Lean and Mathlib at `v4.36.0`. Do not change `lean-toolchain`, `lake-manifest.json` or dependencies.
3. No `sorry`, `admit`, `axiom`, `native_decide`, `unsafe`, `implemented_by`, `extern`, `decide := true` tricks or
   other proof bypasses. Final theorems may depend only on `propext`, `Classical.choice`, `Quot.sound`.
4. No hypotheses beyond the article's standing ones. Allowed: `0 < n` (needed by `tG`), `2 ≤ m`, and
   `m ≤ 2^n` only if a proof truly needs it (try without it first; for `m > 2^n` both sides are `0` in Lean).
5. Do not redefine `tG`, `cost`, `leafDepth`, `greedyRow`, `quality`, `candidateAt` or `Table`. The final theorem
   must be about the existing `tG n m hn` from `Section4/Theorem44.lean`.
6. Do not weaken the statement: no sampled checks, no filter that drops chains in place of a proof, no
   statement that is true for an unrelated reason.
7. Every new module goes into `Section3.roots` in `lakefile.toml`; every final theorem goes into
   `Section3/Check3.lean` (`#check` + `#print axioms`) and `ci/expected_theorems.txt`.
8. Keep all existing results building; do not refactor verified modules beyond adding small helper lemmas.
9. Never claim a theorem is formalized, or a push or CI run succeeded, unless you saw it succeed.
10. **Push after every substantive update.** Each new or changed proved lemma, module, definition set or
    fix that builds is committed and pushed to `section3` at once (after the §6 checks), not batched for
    later; then check PR #1 CI. Nothing that builds stays only local at the end of a step.
11. Toolchain in this environment (if `lake` is not on PATH):
    `export ELAN_HOME=/tmp/claude-1000/-home-aaf-gradient-key/9ad031bf-8603-4891-add2-d33e81d28440/scratchpad/elan PATH=$ELAN_HOME/bin:$PATH`
    (if that directory is gone, install elan into a scratch directory; `lake exe cache get` for Mathlib).

## 1. The statement (from `article.tex`)

Notation, verbatim in substance:

- A **chain** is `s = (s_0,…,s_d)` with `m = s_0 > s_1 > … > s_d ≥ 2`: the sizes of the candidate sets on the
  root path of column 1, down to a fork at depth `d`. `𝒞_{m,n}` = chains with `0 ≤ d ≤ n-1`. For `d = 0`
  products over `j < d` are `1`.
- `a_j = s_j - s_{j+1}`, `q_j = min(a_j, s_{j+1})` for `j < d`; `a_d = s_d`. `q_j` is the quality of the row
  tested at depth `j`.
- Nested candidate sets `[m] = S_0 ⊃ … ⊃ S_d ∋ 1`, `|S_j| = s_j`. **Cells**: `S_j \ S_{j+1}` (`j < d`) and `S_d`.
- `λ_j`: a partition of the integer `a_j`, one per cell. Split each cell into **blocks** of sizes `λ_j`.
  An **assignment** gives one bit to each block (a row constant on each block).
- `W(M)`, `M ⊆ {0,…,d-1}`: number of assignments whose quality on `S_i` is `≤ q_i` for `i ∈ M` and `< q_i`
  for `i ∉ M`, for all `i < d`.
- `V_j(M)`, `j < d`: number of assignments constant on `S_{j+1}`, with the other value on `S_j \ S_{j+1}`, and
  satisfying the conditions of `W(M)` for `i < j`.
- `c(λ) = (-1)^{|λ|-p(λ)} |λ|! / (∏_i λ_i · ∏_v m_v(λ)!)`, with `p(λ)` the number of parts and `m_v(λ)` the
  multiplicity of `v`: the Möbius weight of all set partitions of a cell into blocks of type `λ`.
- `ρ`: injective `{0,…,d-1} → {1,…,n}`, `ρ(j)` = row tested at depth `j`. `M_i = {j : ρ(j) < i}`.

**Proposition 3.1.** With `(2^n)_m = 2^n(2^n-1)⋯(2^n-m+1)`,

    t_{n,m}(G) = (1/(2^n)_m) ∑_{s ∈ 𝒞_{m,n}} ∏_{j<d} C(s_j-1, s_{j+1}-1) ∑_{λ_0,…,λ_d} ∏_{j≤d} c(λ_j) · F_n,

    F_n = ∑_ρ ∏_{i ∉ im ρ} W(M_i) ∏_{j<d} V_j(M_{ρ(j)})   (over all injective ρ).

A chain contributes `0` if for some `j < d` either `q_j (n-j) < s_j - 1` or `max(a_j, s_{j+1}) > 2^{n-j-1}`.

The article's proof (follow it):
1. By symmetry of the columns, `t` is the average of `L_1`, the depth of the leaf of column 1, and this is the
   number of forks whose candidate set contains column 1. So `(2^n)_m t` counts pairs `(A, v)`.
2. For a fork `v` at depth `d` with candidate sets `S_0 ⊃ … ⊃ S_d` and rows `ρ(0..d-1)`: given the sizes, there
   are `∏_j C(s_j-1, s_{j+1}-1)` choices of the sets, each contributing equally.
3. For fixed sets and `ρ`, `A` has this path iff for each `j < d`: row `ρ(j)` is constant on `S_{j+1}` and on
   `S_j \ S_{j+1}` with different values; each row before `ρ(j)` has quality `< q_j` on `S_j`, each row after
   it `≤ q_j`. Rows `ρ(i)`, `i < j`, are constant on `S_j`, so satisfy this automatically. The condition on a row
   depends only on that row.
4. Distinct columns = the only coupling. Möbius inversion on set partitions `Π_m`:
   `1_D = ∑_π μ(π) 1_{E_π}`, `μ(π) = ∏_B (-1)^{|B|-1}(|B|-1)!`.
5. A partition with a block meeting two cells contributes nothing (some `ρ(j)` separates the cells). Otherwise
   the conditions factor by row: row `i` contributes `W(M_i)` or `V_j(M_i)`. Partitions of a cell of size `a`
   of type `λ`, times their `μ`, sum to `c(λ)`.
6. Pruning: at most `n-j` rows are non-constant on `S_j`; each has a side of at most `q_j` columns; at most one
   column lies in none of these sides (two such would agree on every row). So `s_j - 1 ≤ (n-j) q_j`. Rows
   `ρ(0..j)` are constant on each of `S_j \ S_{j+1}` and `S_{j+1}`, so the columns of each part are distinct on
   the other `n-j-1` rows: each part has `≤ 2^{n-j-1}` columns.

**Example (n,m) = (3,4)** (regression tests, §5): `(2^3)_4 = 1680`; chains `(4),(4,2),(4,3),(4,3,2)`. For `(4,2)`:
`C(3,1) = 3`; `c((2)) = -1`, `c((1,1)) = 1`; `V_0 = 2`;
`F_3 = V_0 W({0})^2 + W(∅) V_0 W({0}) + W(∅)^2 V_0`. For `((1,1),(1,1))`: `(W(∅),W({0})) = (10,16)`, `F_3 = 1032`;
`(2)` in exactly one cell: `(6,8)`, `F_3 = 296`; `((2),(2))`: `(2,4)`, `F_3 = 56`. Chain total
`3(1032 - 2·296 + 56) = 1488`. Chains `(4),(4,3),(4,3,2)` give `1680, 144, 96`. Total `3408`, `t_{3,4} = 3408/1680`.

## 2. What already exists (inspect the actual statements before use)

Model (`Section4/GradientKeySection4.lean`, ~line 984):
- `Table n m := Fin n → Fin m → Bool`; `DistinctColumns A` (columns injective); `ValidTable n m` (subtype).
- `ones`, `zeros`, `quality A S r = min (ones A S r) (zeros A S r)`.
- `greedyRow A S hn = (List.argmax (quality A S) (List.finRange n)).getD ⟨0,hn⟩` (first row of largest quality:
  ties broken by row order).
- `candidateStep A S j hn = if S.card ≤ 1 then S else S.filter (fun k => A (greedyRow A S hn) k = A (greedyRow A S hn) j)`.
- `candidateAt A j hn : ℕ → Finset (Fin m)`, `candidateAt 0 = univ`.

`Section4/Theorem44.lean`: `leafDepth A hn j = Set.ncard {i | 2 ≤ (candidateAt A j hn i).card}`;
`cost A hn = (∑_j leafDepth)/m`; `tG n m hn = (∑_{A : ValidTable} cost A.1 hn) / card (ValidTable n m)`.

Useful lemmas:
- `Section4/P1_GreedyPath.lean`: `p1_argmax_some`, `p1_greedy_quality_max`, `p1_greedy_first_max` (tie-breaking),
  `p1_quality_pos_of_diff`, `p1_greedy_step_card_lt`, `p1_path_card_step`, `p1_step_selected_constant`,
  `p1_activeRows*`, `p1_no_row_reuse` (a path uses each row at most once), `p1_candidate_*` (nesting, membership).
- `Section4/Lemma41.lean`: `mem_candidateAt_iff`, `sum_sample`.
- `Section4/DeletedPath.lean`: `argmax_congr`, `argmax_filter`.
- `Section3/TreeDepth.lean`: `candFrom`, `candFrom_fork_bound`, `forksN`, `leafDepth_eq_forksN`,
  `sum_leafDepth_eq_totalDepth`.
- `Section3/Counting.lean`: `validEquiv : ValidTable n m ≃ (Fin m ↪ Word n)`, `card_valid` (`= (2^n).descFactorial m`),
  and the way `tG_sub_completeCost` unfolds `tG`.
- `Section3/Mobius.lean`: `mobF k = (-1)^(k-1) (k-1)!`, `mu c = ∏ i, mobF (c.partSize i)` on
  `OrderedFinpartition m`, `ConstOn c x`, and
  `mobius_injective : ∑ c : OrderedFinpartition m, (if ConstOn c x then mu c else 0) = if Injective x then 1 else 0`.
- `Section3/RowList.lean`: `Row m := Fin m → Bool`, `rq S r` (quality of a row on `S`).

## 3. Indexing and design decisions

- **Column 1** of the article is `0 : Fin m` (needs `0 < m`). Better: prove the per-path identity for an
  arbitrary distinguished column `j₀ : Fin m` and nested sets containing `j₀`. Then `∑_j ∑_A L_j(A)` is `m` copies
  of the same right-hand side, and no separate column-exchangeability lemma is needed.
- **Rows** are `Fin n`, zero-based. The article's `ρ : {0..d-1} → {1..n}` becomes `ρ : Fin d ↪ Fin n`;
  `M_i = {j | ρ j < i}` keeps its form for `i : Fin n` (the order is the same under the shift). "Before `ρ(j)`"
  means `r < ρ j` in `Fin n`. Check this against `p1_greedy_first_max`.
- **Chains**: e.g. `structure Chain (m n) where d : ℕ; s : Fin (d+1) → ℕ; s0 : s 0 = m; anti : StrictAnti s;
  two_le : 2 ≤ s (Fin.last d); hd : d ≤ n - 1` with a `Fintype`/`Finset` of chains (e.g. via strictly decreasing
  lists, or `Finset` of subsets of `{2..m-1}`: a chain is `m` followed by a subset of `{2,…,m-1}` in decreasing
  order, of size `d ≤ n-1`). Choose the representation that makes `∑` and `decide` on the (3,4) example easiest.
- **Partitions `λ_j`**: Mathlib's `Nat.Partition a` (parts as a `Multiset ℕ`). `c λ` as a rational or integer
  (prove it is an integer, or state the formula in `ℚ`/`ℝ`). The sum `∑_{λ_0..λ_d}` is over
  `(j : Fin (d+1)) → Nat.Partition (a j)` (a `Fintype.piFinset`).
- **W and V**: define them computably from the block sizes, so the (3,4) checks run with `decide`/`rfl`.
  An assignment for type `(λ_j)_j` is a function from blocks to `Bool`; the number of ones on `S_i` is the sum
  of the sizes of the blocks with bit `1` in cells `j ≥ i` (`S_i` = union of cells `i..d`), and
  `quality on S_i = min(ones, s_i - ones)`. State a lemma that this is exactly `rq S_i r` / `quality A S_i r` for a
  row constant on the blocks.
- **Sets**: work with `Finset (Fin m)` for `S_j`. Set partitions of a cell: transfer `OrderedFinpartition` along
  `Finset.equivFin`/`orderIsoOfFin`, or prove a Möbius identity for `Finpartition (s : Finset α)` from
  `mobius_injective`. Do not re-prove Möbius inversion from scratch.
- **Real vs ℚ**: `tG` is real. Prove the counting identity in `ℕ`/`ℤ`, then cast once.

## 4. Proof architecture (modules in dependency order)

Suggested modules (adapt names; keep imports acyclic; register each in `Section3.roots`):

1. `PathDefs.lean` — chains, `a`, `q`, cells, blocks, assignments, `W`, `V`, `c`, `F`, the right-hand side `RHS n m`.
   Unit tests: `c` of `(1)`, `(2)`, `(1,1)`, `(3)`, `(2,1)`, `(1,1,1)` (`1, -1, 1, 2, -3, 1`).
2. `PathFork.lean` — **fork counting**:
   `∑_{A valid} leafDepth A hn j₀ = ∑_{d} #{A valid | 2 ≤ |candidateAt A j₀ hn d|}` and every fork has depth
   `≤ n-1` for valid `A` (use `candFrom_fork_bound` / `p1_no_row_reuse`). Then `(2^n)_m · tG = (1/m)∑_{j₀}…`.
3. `PathSets.lean` — **paths as nested sets**: for valid `A`, the sequence `candidateAt A j₀ hn 0..d` with
   `|S_d| ≥ 2` is a strictly decreasing nested family containing `j₀`, starting at `univ`; conversely group
   the count by that family. **Counting the families**: for a fixed chain, the number of nested families
   `univ = S_0 ⊃ … ⊃ S_d ∋ j₀` with `|S_j| = s_j` is `∏_{j<d} C(s_j - 1, s_{j+1} - 1)` (induction on `d`,
   `Finset.card_powersetCard` on `S_j.erase j₀`).
4. `PathGreedy.lean` — **greedy characterization**: for fixed nested `S` and `ρ`,
   `(∀ j ≤ d, candidateAt A j₀ hn j = S_j)` iff for every `j < d`: `ρ j = greedyRow A S_j hn`, which is
   equivalent to the row-wise conditions of §1 step 3 (strict `<` before `ρ j`, `≤` after, and `ρ j` constant on
   `S_{j+1}` and on `S_j \ S_{j+1}` with different values, with `j₀ ∈ S_{j+1}`). Also prove `ρ` is determined by
   `A` (so `[path] = ∑_ρ ∏_rows [row condition]`) and that rows `ρ i`, `i < j`, satisfy the depth-`j`
   condition automatically (quality `0`). Watch `min` vs strict inequality, `S.card ≤ 1` branch of `candidateStep`.
5. `PathFactor.lean` — **row independence**: for fixed `S`, `ρ` and a set partition `π` of `Fin m`,
   `#{A : Table | path conditions ∧ A constant on blocks of π (rowwise)} = ∏_{r : Fin n} (#admissible rows r)`
   (`Fintype.card_pi` / `Finset.prod_univ_sum`).
6. `PathMobius.lean` — **Möbius step**: `#{A valid with path S} = ∑_π μ(π) ∏_r (#admissible rows of r constant
   on π)`, from `mobius_injective` applied to the column map `j ↦ (r ↦ A r j)`.
7. `PathCells.lean` — **cell restriction**: if a block of `π` meets two cells, the factor of row `ρ j` for the
   separating `j` is `0`. Non-crossing `π` ≃ tuples of set partitions of the cells, with `μ` multiplicative.
8. `PathCoeff.lean` — **cellwise coefficient**: the row factors depend only on the block-size types; the number
   of set partitions of an `a`-set of type `λ` is `a! / (∏ λ_i! ∏ m_v(λ)!)`, so `∑_{type π = λ} μ(π) = c(λ)`.
   Prove this by a counting argument or a recurrence, plus the small-value tests.
9. `PathChain.lean` — **per-chain identity** (the key theorem): for every chain `s` with `d ≤ n-1`, every
   `j₀` and every nested family `S` of sizes `s` containing `j₀`,
   `#{A valid | ∀ i ≤ d, candidateAt A j₀ hn i = S_i} = ∑_λ ∏_{j≤d} c(λ_j) F_n(s, λ)`.
   Summed over the families: `∏ C(…) · ∑_λ ∏ c · F_n = #{(A, fork at depth d of chain s on the path of j₀)}`.
10. `PathFormula.lean` — **Proposition 3.1** and **pruning**:
    - `prop_path_formula (hn : 0 < n) (hm : 2 ≤ m) : tG n m hn = (1/((2^n).descFactorial m : ℝ)) * ∑_{s ∈ 𝒞_{m,n}} …`
      with the exact right-hand side of §1.
    - `chain_occurs_bounds`: if a valid `A` has a fork with chain `s` on the path of `j₀`, then for all `j < d`,
      `s_j - 1 ≤ (n - j) q_j` and `max(a_j, s_{j+1}) ≤ 2^{n-j-1}` (prove both from the table, as in §1 step 6;
      `p1_activeRows_budget` may help with the first).
    - `prop_path_prune`: if either inequality fails for some `j < d`, then the chain's term
      `∏ C(…) · ∑_λ ∏ c · F_n` equals `0` (from the per-chain identity and `chain_occurs_bounds`).

## 5. Regression examples (in `Section3/PathExamples.lean`)

Using the definitions of `PathDefs` (not hand-typed constants):
- chain `(4,2)`, `n = 3`: `(W ∅, W {0}) = (10,16)`, `(6,8)`, `(2,4)` for the three `λ` types; `V_0 = 2`;
  `F_3 = 1032, 296, 56`; chain term `1488`;
- chain terms `1680, 1488, 144, 96` for `(4), (4,2), (4,3), (4,3,2)`; `RHS 3 4 = 3408 / 1680`;
- and, via `prop_path_formula`, `tG 3 4 _ = 3408/1680` (compare with the existing `example_n3_m4`).
Use `decide` or `rfl` on computable definitions (no `native_decide`). If kernel reduction is slow, evaluate
`W`/`V` by small lemmas or `simp` with `Finset.sum`/`Fintype.card` unfolding, but keep the definitions the same.

## 6. Verification after every milestone

1. `lake build` (all targets) passes.
2. `python3 ci/check_proofs.py` passes (shortcut scan, Lake roots, axiom reports).
3. `lake env lean Section3/Check3.lean` and `lake env lean Section4/Check.lean`; every new final theorem shows
   only `[propext, Classical.choice, Quot.sound]` (or a subset).
4. Read each public statement and check it says what the article says (hypotheses, indices, strict vs `≤`).
5. Update `FORMALIZATION_STATUS.md` (row for Proposition 3.1: declarations, modules, what is verified,
   what remains), `ci/expected_theorems.txt`, `logs/check3.log`.
6. Commit to `section3`, `git push origin section3` (no force), then watch PR #1 CI
   (`gh pr checks 1 --watch` or `gh run list --branch section3`). Fix failures before the next milestone.

Suggested milestones: (A) definitions + `c` tests + (3,4) `W`/`V`/`F` tests; (B) steps 2–4; (C) steps 5–8;
(D) per-chain identity; (E) Proposition 3.1 and pruning; (F) the `tG 3 4` check via the formula, docs, PR text.

## 7. Pitfalls seen before in this repository

- Missing `Decidable` instances: `open Classical` locally; prefer `Finset.filter` with decidable predicates in
  computable definitions.
- Dependent coercions (`Fin` casts, subtypes): add `rfl` "apply" lemmas and explicit `(α := …)` arguments.
- `.inj` vs `.injective`; `Nat.Ico_succ_right` → `Finset.Ico_add_one_right_eq_Icc`; big `Nat.choose` via `rfl`.
- Natural-number subtraction (`s_j - 1`, `n - j`, `n - j - 1`), empty products (`d = 0`), empty types
  (`Fin 0 ↪ Fin n`), `Finset` vs `Fintype` sums, casts `ℕ → ℤ → ℝ`, `(-1)^k` in `ℤ`.
- Set partitions vs integer partitions; `OrderedFinpartition` orders parts by largest element.
- A helper statement that compiles but does not imply the article's result: check each one.

## 8. Report after each push

**Commit** (full SHA) · **Branch** `section3` · **PR** #1 · **Results completed** (Lean names ↔ article) ·
**Files changed** · **Local build** pass/fail · **Shortcut scan** pass/fail · **Axiom audit** (actual sets) ·
**GitHub CI** (run URL, conclusion) · **Remaining work** (exact open obligations) · **Next step**.

## 9. Done when

- `prop_path_formula` (full formula, connected to the existing `tG`) and `prop_path_prune` (both pruning
  conditions, derived from the table, not assumed) compile;
- the per-chain identity, the family count, the greedy characterization, the Möbius/cell steps and `c(λ)` are
  proved as stated in §4;
- the (3,4) regression checks of §5 pass on the actual definitions;
- all new modules are Lake roots, the axiom audit passes, `FORMALIZATION_STATUS.md`, `README.md` and the PR #1
  description are updated, everything is pushed to `section3`, and PR #1 CI is green.

Do not merge PR #1. If a step cannot be finished, push the verified part, mark the rest "not yet formalized"
in `FORMALIZATION_STATUS.md`, and report the exact open obligation.
