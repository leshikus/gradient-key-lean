# gradient-key-lean

Lean 4 proof of Theorem 4.4 of *The gradient key on random tables* (Section 4: Lemmas 4.1–4.3 and Theorem 4.4).
Code and data of the article: [gradient-key-impl](https://github.com/leshikus/gradient-key-impl). MIT licence.

The final theorem is `GradientKey.Concrete.theorem_4_4` in `Section4/Theorem44.lean`:

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
lake build                          # builds GradientKey and Section4
lake env lean Section4/Check.lean   # prints the theorem, the definitions and the axioms
```

Lean and Mathlib are pinned to `v4.36.0` (`lean-toolchain`, `lakefile.toml`, `lake-manifest.json`).
CI (`.github/workflows/lean.yml`) runs `lake build` on every push and pull request.

## Layout

- `Section4/`: the proof; `Section4/STATUS.md` maps each result to its declaration.
- `drafts/original/`: the P0–P10 drafts as received, unchanged.
- `logs/`: compiler output before and after the repairs, and the Python regression runs.
