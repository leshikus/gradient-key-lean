# Lean Section 4 proof: source bundle

This package contains the available Lean source candidates, status reports,
regression checks, and original P0–P10 task prompts, with original file
extensions restored from indexed text exports. `GradientKeySection4.lean`
was recovered in full from overlapping text chunks: its 1,735 lines total
67,988 bytes, matching the source file metadata. None of these candidate
Lean proofs was previously machine-compiled, as their status files explain.

## Important unavailable original files

The following two files were listed by the master prompt but could not be
copied as bytes from Project/Library storage. They are **not** in this ZIP:

- `article.tex` — original authoritative paper TeX (available in user's
  project attachments; attach separately when using `MASTER_PROMPT.md`).
- `P0_Lean_Baseline_Project.zip` — original P0 reproducible-build scaffold.

These were not recreated, because an approximate replacement or a fabricated
archive would be misleading. The other 43 source and status files and the
master prompt are included. To use the formalization project, supply the
original `article.tex` separately and establish a working Lean/Mathlib setup
(as described in `P0_REPORT.md`).

## Suggested entry points

1. `MASTER_PROMPT.md` — overall integration instruction.
2. `P0_REPORT.md` — baseline and toolchain status.
3. `P9_Audit.md` and `P9_patch.diff` — important local correction.
4. `GradientKeySection4.lean` and `GradientKeySection4_STATUS.md`.
5. All `P1_...` through `P8_...` files and `P10_integration.md`.

This bundle is a collection of unverified drafts for further compilation,
not a working or certified Lean project.
