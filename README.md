# gradient-key-lean

Lean 4 formalization of the proofs of the article *The gradient key on random tables*.
Code and data of the article: [gradient-key-impl](https://github.com/leshikus/gradient-key-impl). MIT licence.

```sh
lake exe cache get   # Mathlib build cache
lake build
```

CI (`.github/workflows/lean.yml`) runs `lake build` on every push and pull request.
Toolchain and Mathlib are pinned to `v4.36.0` (`lean-toolchain`, `lakefile.toml`).
