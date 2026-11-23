# gradient-key-lean

Lean 4 proofs of results of *The gradient key on random tables*: Propositions 3.1 (the path formula and its
pruning claim), 3.2, 3.4, 3.5 and Corollary 3.3 (Section 3), and Lemmas 4.1–4.3 and Theorem 4.4 (Section 4).
The computations of Section 3 are not formalized. `FORMALIZATION_STATUS.md` maps each result to its declaration.
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
lake build                          # builds GradientKey, Section3 and Section4
lake env lean Section4/Check.lean   # prints the theorem, the definitions and the axioms
lake env lean Section3/Check3.lean  # the same for Section 3
```

Lean and Mathlib are pinned to `v4.36.0` (`lean-toolchain`, `lakefile.toml`, `lake-manifest.json`).
CI (`.github/workflows/lean.yml`) runs `lake build` on every push and pull request.

## Layout

- `Section3/`: Propositions 3.2, 3.4, 3.5 and Corollary 3.3; module list in `FORMALIZATION_STATUS.md`.
- `Section4/`: the proof; `Section4/STATUS.md` maps each result to its declaration.
- `drafts/original/`: the P0–P10 drafts as received, unchanged.
- `logs/`: compiler output before and after the repairs, and the Python regression runs.
