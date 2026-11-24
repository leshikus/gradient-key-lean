# Contributing

## Repository

- Branch `main` only: no other branches, no pull requests, no force-push, no history rewrite. The article cites
  commits of this repository (`140d441`, `cecd8c9`, `aa1652f`); they must stay reachable.
- The article (`leshikus/gradient-key`, `article.tex`) is the authority for statements.

## Toolchain

- Lean and Mathlib `v4.36.0`, pinned in `lean-toolchain` and `lake-manifest.json`. Do not run `lake update`.
- `lake exe cache get`, then `lake build`.

## Proof rules

- Forbidden in every `.lean` file: `sorry`, `admit`, user `axiom`, `unsafe`, `native_decide`, `implemented_by`,
  `@[extern]`, `debug.skipKernelTC`. `ci/check_proofs.py` rejects them.
- Final theorems depend only on `propext`, `Classical.choice` and `Quot.sound`.
- No hypotheses beyond the article's, no weakened statements, no redefined model: reuse `tG`, `ValidTable`,
  `candidateAt`, `PathChain`, `pathChainTerm`, `pathFormulaRHS`, `numer`, `Bint`.
- `decide` only where the kernel check takes a few seconds; `set_option maxHeartbeats` only on one declaration,
  with a comment.
- Computed values are checked by the kernel; external computations are proof targets only.

## After every change

1. Register each new module in the `roots` of its library in `lakefile.toml`.
2. In `Section3/Check3.lean` (or `Section4/Check.lean`) add `import <Module>`, `#check @thm` and `#print axioms thm`
   for each final theorem; add its name to `ci/expected_theorems.txt`.
3. Add a row to `FORMALIZATION_STATUS.md`: article result, Lean declaration, module.
4. Locally, if Lean is available:
   ```
   lake build
   lake env lean Section3/Check3.lean > /tmp/check3.log
   lake env lean Section4/Check.lean > /tmp/check4.log
   python3 ci/check_proofs.py /tmp/check3.log /tmp/check4.log
   ```
5. Commit, push to `main`, and confirm that CI (`.github/workflows/lean.yml`, the same checks) passes for that commit.

## Known pitfalls

- Most Section 3 files `open Classical`; decidable or `Fintype` instance mismatches appear as type mismatches between
  identical-looking terms. Use `convert … using k`, `Subsingleton.elim`, or `Fintype.card` of a subtype.
- "motive is not type correct" in `rw` on a natural number inside a type: use `Eq.trans`, `subst`, or `have` + `omega`.
- `rw` closes goals by `rfl`; follow it with `all_goals` when a case may already be closed.
- `Function.Involutive f` does not rewrite with `simp`; state `f (f x) = x` as a lemma.
- `if_pos`, `if_neg` give deprecation warnings only.
