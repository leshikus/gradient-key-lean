# P0 — Lean 4 baseline: environment assessment, pinned project, and API patch

Date: 2026-11-21. **STATUS: NOT COMPILED.**

## What was actually inspected

* `article.tex` (Section 4, Lemmas 4.1–4.3 and Theorem 4.4) from the current uploads.
* `GradientKeySection4.lean` v4 (~1,735 lines) from the user's project Library, as readable text through Files. The raw bytes could **not** be materialized into this container.
* `GradientKeySection4_STATUS.md` v4, which explicitly states that the source was not compiler-checked and that the theorem remains conditional.

A native filesystem check found neither `lean`, `lake`, `elan`, nor Mathlib; DNS lookups for `github.com` and `releases.lean-lang.org` failed. These are environment-level observations, **not Lean compiler diagnostics**.

## Pinned reproducibility target (not executed here)

* Lean toolchain: `leanprover/lean4:v4.34.1`.
* Mathlib4 revision: `d13f23b723b8a846827a245b89c10fc7d3f11612` (matching Lean v4.34.1).
* The supplied `lakefile.toml` and `lean-toolchain` encode these dependencies.
* No `lake-manifest.json` was generated because `lake update` cannot run in this environment. On an online build host, generate and commit that manifest to pin Mathlib's transitive dependencies.

## What P0 provides

* `P0_APIProbe.lean`: API name checks and a computational tie-breaking probe. **Not compiled.**
* `P0_export_api.py`: an exact text-only patch generator. With the v4 source present, it creates `P0_BaselineFixed.lean` and a unified diff. The generator changes only the *visibility modifiers* of nine existing declarations. Its mechanical inverse check proves the remaining text is unchanged. It does **not** claim to repair compiler errors or prove mathematics.
* `P0_build.sh`: collects original compiler diagnostics **before** creating and compiling the visibility-patched candidate. Writes logs to `P0_logs/` and returns failure on a failed compile.

There is deliberately no substitute `P0_BaselineFixed.lean` pretending to be the complete baseline. It can only be generated from the original full source, which is not accessible as raw bytes here.

## External API audit: concrete source locations

| Source line | Declaration | Finding / action |
| ---: | --- | --- |
| ~95 | `split_size_identity` | Algebraic statement agrees with the two-child mean identity in Lemma 4.1. No compiler validation. |
| ~323–365 | `logb_two_chord`, `binary_window_chord` | Matches mathematical chord argument; library lemma elaboration remains untested. |
| ~369–388 | `nat_log_binary_window`, `nat_log_pos_and_le` | Corresponding Mathlib `Nat.log` theorem names exist in public docs; arguments/unification not tested. |
| ~644 | `theorem_4_4_all_from_probabilistic_lemmas` | **Retain entire statement and all explicit hypotheses**; it is a conditional result, not the complete paper theorem. |
| ~715–754 | `finiteAverage` and its helper lemmas | Defined `private`; export visibility so other modules can cite the exact finite uniform expectation API. |
| ~1012–1016 | `greedyRow` using `List.argmax` | Mathlib documents **first occurrence on ties**. With `List.finRange n` increasing, this is consistent with the article's first-row rule. Preserve. |
| ~1107–1119 | `finiteAverage_finset_sum`, `finiteAverage_div` | Export visibility for row-moment and averaging agents. Proof tactics require compiler verification. |
| ~1217 | `Equiv.sum_comp` | Public Mathlib API exists; exact term invocation must be compiled. |
| ~1491–1512 | `Finset.sum_involution` | Public Mathlib API exists; dependent partner and sum-cancellation proof require elaboration check. |
| ~1629 | `conditional_inserted_imbalance_exact` | Retain statement *verbatim*, including validity of extensions and pair-closed candidate sets. **No mathematical weakening.** |
| ~1665 | `mean_imbalance_from_unused_rows` | Explicit pointwise and row-mean hypotheses remain; connecting them to concrete sampled greedy paths is another agent's obligation. |

**None** of the above locations is an observed compiler error. Error types (parse / scope / Mathlib API / proof failure) cannot be assigned to unrun compilations. A line-by-line compiler blocker list must be produced from `P0_logs/original.log` when Lean is available.

## Which declarations need a public API?

At minimum `GradientKey.finiteAverage` and its `finiteAverage_const`, `finiteAverage_nonneg`, `finiteAverage_mono`, `finiteAverage_add`, `finiteAverage_sum`, `finiteAverage_finset_sum`, and `finiteAverage_div` helpers should be referenceable from separately compiled agents. `finiteCard_pos` is exported as well to support denominator-positivity arguments. Their original mathematical types and proofs do not change. No `axiom`, `sorry`, or extra hypothesis was inserted.

## Source dependencies still NOT discharged by P0

* Concrete greedy tree: path termination, tested rows are not repeated, forks split, path-tail bound.
* The expected candidate-size transition of Lemma 4.1.
* The deletion/insertion conditioning bridge, pair-closure, and agreement with the row-deleted tree.
* The Hoeffding tail of Lemma 4.2 and the logarithmic Lemma 4.3 bound.
* The theorem's transition and imbalance inputs remain explicit hypotheses. A compiling version would still not constitute the unconditional Theorem 4.4 until these are proved and connected.

## Exact build procedure on a host with Lean / network access

1. Place the **unchanged** `GradientKeySection4.lean` v4 file in this directory.
2. Verify that the system has Elan and can reach GitHub.
3. Run `bash P0_build.sh`. It will generate `P0_logs/environment.txt`, `P0_logs/lake-update.log`, `P0_logs/api-probe.log`, `P0_logs/original.log`, `P0_logs/export.log`, and `P0_logs/api-exported.log`.
4. Examine the original diagnostics before modifying proof code. `P0_BaselineFixed.lean` will contain the minimal export patch only.
5. Group compiler errors by their **actual** emitted location and cause. Change only those lines in the candidate, never the original, and re-run `lake env lean P0_BaselineFixed.lean`.
6. Commit the generated `lake-manifest.json` with the exact source hash and toolchain once the build is successful.

To run the original command directly (after `lake update; lake exe cache get`):

```sh
lake env lean GradientKeySection4.lean
```

## Merge plan

1. Obtain raw v4 baseline and run the unmodified compile.
2. Merge the public `finiteAverage` API export after the original has a successful build, or keep it in `P0_BaselineFixed.lean` during triage.
3. Fix genuine Mathlib API/Lean syntax errors in the candidate without changing statement signatures.
4. Have mathematical agents import the compiling baseline and prove their separate lemma obligations.
5. Only then integrate and compile the unconditional Section 4 proof.
