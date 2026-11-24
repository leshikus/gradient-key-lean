# gradient-key-lean

Lean 4 proofs of results of *The gradient key on random tables*: Lemma 3.1, Propositions 3.2 (the path formula and its
pruning claim, the example (3,4) and the row-by-row recurrence for F_n), 3.3 (with the integrality of the B_k and the
rationality of the a_j), 3.5, 3.6
and Corollary 3.4 (Section 3), and Lemmas 4.1–4.3 and Theorem 4.4 (Section 4).
Also: `t_{3,5} = C(5) < t_{4,5}`; the 41 exact values for `n ≤ 6` given by Propositions 3.3, 3.5 and 3.6, and Table 2 rows
`n ≤ 3`; the integrality of `(2^n)_m t_{n,m}(G)` and the uniqueness of the `a_j` from `N_m(0),…,N_m(M-1)`; the reduction to missing
sets containing `0`; the maximum-length formula. The other computations of Section 3 are not formalized.
`FORMALIZATION_STATUS.md` maps each result to its declaration.
Code and data of the article: [gradient-key-impl](https://github.com/leshikus/gradient-key-impl). MIT licence.

The final theorem of Section 4 is `GradientKey.Concrete.theorem_4_4` in `Section4/Theorem44.lean`:

```
theorem_4_4 : ∀ (n m : ℕ) (hm : 2 ≤ m) (hsize : m ≤ 2 ^ n),
  tG n m ⋯ ≤ displayedBound n m ∧
    tG n m ⋯ < Real.logb 2 ↑m + 2 + 2 * Real.log (2 * ↑(Nat.log 2 m)) ∧
      tG n m ⋯ < Real.logb 2 ↑m + 1 + (↑(Nat.log 2 m) - 1) / (↑n - ↑(Nat.log 2 m) + 1) ∧
        (2 * Nat.log 2 m - 2 ≤ n → tG n m ⋯ < Real.logb 2 ↑m + 2)

'GradientKey.Concrete.theorem_4_4' depends on axioms: [propext, Classical.choice, Quot.sound]
```

`tG n m` is `t_{n,m}(G)`: the average over binary `n × m` tables with distinct columns of `(1/m) ∑_j L_j`, where `L_j` is the
number of depths with a fork on the path of column `j`, and `G` tests the first row of largest quality `min(k, s-k)`.

## Build

```sh
lake exe cache get                  # Mathlib build cache
lake build                          # builds Section3 and Section4
lake env lean Section4/Check.lean   # prints the theorem, the definitions and the axioms
lake env lean Section3/Check3.lean  # the same for Section 3
```

Lean and Mathlib are pinned to `v4.36.0` (`lean-toolchain`, `lakefile.toml`, `lake-manifest.json`).
CI (`.github/workflows/lean.yml`) runs `lake build`, both checkers and `ci/check_proofs.py` on every push.
Rules for changes: `CONTRIBUTING.md`.

## Layout

- `Section3/`: the mathematical results of Section 3; module list in `FORMALIZATION_STATUS.md`.
- `Section4/`: the proof; `Section4/STATUS.md` maps each result to its declaration.
- `ci/`: `check_proofs.py` (shortcuts, roots, axioms), `expected_theorems.txt`, `generate_exact.py` (exact values from
  `data/fixed_n.csv`, a copy of `gradient-key-impl/data/small/fixed_n.csv`).
- `drafts/`: the prompt of the current review. The original drafts and compiler logs are in the history (`aa1652f`).
