# Prompt: formalize the remaining claims of Section 3 of *The gradient key on random tables*

You are a Lean 4 + Mathlib formalization engineer. Work in `leshikus/gradient-key-lean` on `main` (cecd8c9 or later).
The article is `article.tex` in `leshikus/gradient-key` (642973e or later), and the data is in
`leshikus/gradient-key-impl` (`data/small/`, `data/gradient-bound/`). The statements in the article are authoritative.
`FORMALIZATION_STATUS.md` lists what is already proved: Lemma 3.1, Propositions 3.2, 3.3, 3.5 and 3.6, Corollary 3.4,
and Section 4. Do not redo any of it.

## 0. Ground rules

- **Branches:** use `main` only. Create no branches and open no PRs. Do not force-push, squash or rewrite history.
  The article cites commits `140d441` and `cecd8c9`, so both must stay reachable from `main`.
- **Toolchain:** Lean and Mathlib `v4.36.0`. Do not run `lake update`.
- **Forbidden outside `drafts/`:** `sorry`, `admit`, user `axiom`, `unsafe`, `native_decide`, `implemented_by`,
  `@[extern]` and `Lean.ofReduceBool`. A computed value counts as proved only when the kernel checks it,
  with `decide`, `decide +kernel` or `rfl`.
- **Kernel budget:**
  - A single declaration may take at most 60 s of kernel time. Use `set_option maxHeartbeats`/`maxRecDepth` per
    declaration only, with a comment that gives the measured time.
  - The whole CI run must stay under 20 min.
  - If an instance exceeds the budget, leave it out and list it as **not formalized** in `FORMALIZATION_STATUS.md`.
    Never weaken a statement to make it fit.
- **Hypotheses:** use only the article's (`2 ≤ m ≤ 2^n`, `0 < n`, and similar). Every final theorem must depend only on
  `propext`, `Classical.choice` and `Quot.sound`.
- **New modules:** each one is `Section3/<Name>.lean`, listed in `roots` of the `Section3` library in `lakefile.toml`.
  Add final theorems to `Section3/Check3.lean` and `ci/expected_theorems.txt`.
- **After each step that compiles:**
  1. `lake build` exits 0;
  2. `python3 ci/check_proofs.py` passes;
  3. `lake env lean Section3/Check3.lean > logs/check3.log` shows only the three axioms;
  4. update `FORMALIZATION_STATUS.md` (article claim → declaration → file; move items out of "Not formalized");
  5. commit, `git push origin main`, and check CI with `gh run list -L 1`. Report the commit hash and the CI result.
- **Known pitfalls:**
  - Do not `open Classical` globally; use `open Classical in` per declaration.
  - `omega` fails on distinct but defeq atoms; state the equality with `rfl` first.
  - Kernel reduction of `Finset.sum` over `Fintype` instances (`Fin n ↪ Fin m`, `OrderedFinpartition`) is slow.
    For computation, write `List`/`Nat`-recursive definitions and prove them equal to the existing ones.
    Kernel `Nat` arithmetic is GMP-accelerated; `ℚ` and `Finset` are not.

## 1. Maximum length (the "Maximum length" paragraph after Table 1)

Claim: let `L_max = max_j L_j`, let `t^max_{n,m}(G)` be its average over `𝒜_{n,m}`, and define `B^max_k` with
`L_max − ⌈log m⌉` in place of `X̄`. Then the formula of Proposition 3.3 holds for `t^max_{n,m}(G) − ⌈log m⌉`.

1. **`SmallMGen`:** generalize `sum_excess_eq` / `prop_small_m` (`Section3/SmallM.lean`) to any
   `Φ : List (Row m) → ℤ` that
   - is invariant under `canon` and `firsts`, and
   - vanishes unless `Sep L`.

   The proof should be the existing one with `excessL` replaced by `Φ`. Then re-derive `prop_small_m` as an
   instance, keeping its statement and name unchanged.
2. **`MaxLength`:**
   - define `lmax L` (the largest leaf depth of the tree of the row list `L`), `tGmax n m hn` on `ValidTable n m`,
     and `BmaxInt`/`coeffAmax`/`numerMax`;
   - prove `lmax` invariant under `canon` and `firsts` (from `ldepth_congr`-style lemmas on `lcand`);
   - prove `prop_max_length : tGmax n m hn − Nat.clog 2 m = numerMax n / (2^n).descFactorial m` together with the
     Stirling form.

   The article claims only the formula, so prove only that. Optional lemmas such as `BmaxInt ≥ 0` may be added
   if they are proved.

## 2. Interpolation (the "Computation" paragraph)

1. **`Interpolation`:**
   - Uniqueness: if `∑_{j=1}^M a_j (2j)^n = ∑_{j=1}^M b_j (2j)^n` for `n = 0,…,M−1`, then `a = b`. Use
     `Matrix.det_vandermonde`; the nodes `2,4,…,2M` are distinct.
   - Corollary `coeffA_determined`: the `a_j` of Proposition 3.3 are the unique solution of the system with
     right-hand sides `N_m(0),…,N_m(M−1)`. Use `numer_zero` and `prop_small_m`.
   - Integrality: `(2^n)_m · t_{n,m}(G)` is a natural number, namely `∑_A ∑_j L_j / m` per column symmetry
     (`chain_term_natural` or `sum_ldepth_eq`). Also `N_m(n) = (2^n)_m t_{n,m}(G) − (2^n)_m C(m)`.
2. **`PathEval`, a kernel-checkable evaluator of the path formula:**
   - Define `pathEval n m : ℕ` by `List`/`Nat` recursion only:
     - chains as lists;
     - partition types `λ_j` as sorted lists;
     - `c(λ)` as a pair (sign, natural numerator) with exact division;
     - `W` and `V_j` by enumerating `Bool` assignments on blocks;
     - `F_n` by the recurrence `D_{i+1}(M) = D_i(M)W(M) + ∑_{j∈M} D_i(M∖{j})V_j(M∖{j})`, with `M` a bitmask `ℕ`.
   - The value is the integer `(2^n)_m t_{n,m}(G)`; signed intermediate sums may use `ℤ`.
   - Prove `pathEval_eq : (pathEval n m : ℝ) = (2^n).descFactorial m * tG n m hn`, from `prop_path_formula`,
     `pathF_eq_pathD` and lemmas that equate each list definition with its `Finset` counterpart.
   - Sanity check by `decide`/`rfl`: `pathEval 3 4 = 3408`.

## 3. Instances (each its own commit; stop each item at the kernel budget)

1. **`t_{3,5}(G) = C(5) < t_{4,5}(G)`** (the sentence after Corollary 3.4), from `pathEval_eq`.
2. **Displayed formulas for `m = 4, 5, 6`** (`small_formulas.tex` in the article repo):
   - `N_4(n) = −3/4·2^n + 2·4^n − 3/2·6^n + 1/4·10^n`, and the corresponding formulas for `N_5`, `N_6`.
   - Route: compute `N_m(n)` for `n < M = 2^{m−1}` with `pathEval` (`n ≤ 7`, `15`, `31`), check that the stated
     `a_j` satisfy these `M` equations, and conclude by `coeffA_determined`. This uses `n ≥ 1` with `n` up to
     `M − 1`, and also `n < ⌈log m⌉`, where `N_m(n) = 0` by `numer_eq_zero_of_two_pow_lt`; there `pathEval` is
     not needed.
   - Name the theorems `small_formula_four`, `small_formula_five`, `small_formula_six`.
   - Cross-check `m = 4` independently: compute `B_1,…,B_8` from a list-based copy of `Bint` over the 8 row types,
     proved equal to `Bint`; use `alt_sum_Bint`/`NumerZero` to drop the constant row type if needed.
3. **Table 1, rows `m = 4, 5, 6`:** `J`, `A_m = B_J/J!` and `r_m = J/2^{m−1}`, from item 2 and `coeffA_J`. Also prove the
   caption's "the rates `r_m` are not monotone in `m`" from `r_4 = 5/8 > r_5 = 3/8 < r_6 = 1/2`.
   - Try `m = 7` (`M = 64`; `n ≤ 63`). Measure before committing to it.
   - Rows `m ≥ 8` need `M ≥ 128` evaluations and are expected to exceed the budget. List them as not formalized
     unless you find a kernel-checkable route.
4. **Exact values for `n ≤ 6`** (`data/small/fixed_n.csv`, `data/small/exact_values.md`): for every pair `(n,m)` with
   `2 ≤ m ≤ 2^n`, `n ≤ 6`, prove `t_{n,m}(G)` equals the file's exact value.
   - Pairs near the full cube follow from `prop_dense`, `prop_near_dense_one` and `prop_near_dense_two`.
   - Other pairs follow from `pathEval_eq` plus `decide`.
   - Generate the Lean statements from the CSV with a script in `ci/` (commit the script). Group many pairs per
     module so that each module builds in under 5 min.
   - Record which pairs fit the budget. The pairs `(6, 52…55)` are known to be the costliest for the path formula.
5. **Table 2 (`tab:small-n`) and the sentence after it:** for each `n ≤ 6`, prove the maximum of `t_{n,m}(G) − C(m)` over
   `2 ≤ m ≤ 2^n` and, for `n ≥ 3`, the `m` where it is attained, `m = 2^{n−1}`. Prove also that it increases with `n` for
   `n = 3,…,6`. This needs every pair of item 4 for that `n`; formalize only the `n` for which all pairs are proved.

## 4. Enumeration of the missing words (Section 3.3)

1. **`Translation`:** for `v : Word n`, translating every column by `w ↦ w ⊕ v` complements the rows `i` with `v_i = 1`.
   It keeps every quality and the depth sum of `G`; use `canon`-style invariance (`rq_canon`, `ldepth_map_canon`).
2. **`missing_mean_eq`:** the mean of the depth sum of `G` over the sets `R` of `r ≥ 1` missing words equals the mean over
   the sets with `0 ∈ R`. Prove it by the double count in the article: `(R, w) ↦ (R ⊕ w, w)` with `w ∈ R` is a bijection
   onto the pairs `(R', w)` with `0 ∈ R'`; `R` occurs in `r` pairs and `R'` in `2^n` pairs.
3. Engine agreement statements (`gradient_complement` and the C++ engines) are claims about programs, not about `t`.
   Do not formalize them; list them as not formalized.

## 5. Finish

- `FORMALIZATION_STATUS.md`:
  - one row per new claim;
  - an updated "Not formalized" list naming exactly the pairs and rows left out, with the measured reason
    (e.g. "kernel time over 60 s at (6,53)").
- `README.md`: one line on the new results.
- Do not edit `article.tex`. In the final report, give:
  - the final commit hash;
  - the list of newly proved article claims;
  - the list left out.

  The authors then update the Lean citation sentence in Section 3.4 ("Programs and data").
