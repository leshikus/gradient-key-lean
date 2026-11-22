# P2 integration notes — Lemma 4.1

**Status: NOT COMPILED.** The provided Lean source is an independent finite-partition development; it does not yet discharge the bridge to the concrete greedy `FinitePathData`.

## What the abstract result establishes

For any finite column set `J`, any `key : J → C` describing a partition into fibres, and any `bit : J → Bool`, `finite_partition_recurrence` states exactly

    ∑_j (child_size(j)-1)
      = (∑_j(parent_size(j)-1) - ∑_j 1_{parent_size(j)≥2}
         + ∑_j imbalance(parent(j))) / 2.

It proves the weighting of each parent by its number of columns by `sum_by_fiber`, avoiding an unsupported appeal to conditional uniformity. It explicitly assigns fork indicator and imbalance zero at singleton parents. No row-distribution assumption is used.

## Concrete integration obligation (P1 or P10)

In `GradientKey.Concrete`, for each fixed valid matrix `A` and level `i`, take:

    key j := candidateAt A j hn i
    bit j := A (greedyRow A (key j) hn) j

Then prove the following two equalities for every `j : Fin m`:

1. `candidateAt A j hn i = P2.fiber key (key j)` (the candidate sets at level `i` form fibres).
2. `candidateAt A j hn (i+1) = P2.fiber (fun k => (key k, bit k)) (key j, bit j)` (the two children form the refined fibres).

The first equality follows by induction using: each column is in its own candidate set, candidate sets meeting at a column are equal, and the selected greedy row depends only on the candidate set. The second uses `candidateStep` and the singleton case; for a singleton `S={j}` the bit-filter of `S` selecting `bit j` is exactly `S`. These facts do **not** require the row to split, so they can be proved before P1 establishes strict descent and termination. The order of `List.argmax` is preserved: both members of one cell call `greedyRow` with literally the same `S`.

Once these obligations are supplied, apply `finite_partition_recurrence` separately to every fixed table `A`. Sum over the finite type `ValidTable n m` and divide by `(Fintype.card (Sample n m) : ℝ)` to obtain the exact statement

    ∀ i, P.expectedExcess (i+1) =
        (P.expectedExcess i - P.forkProb i + P.expectedImbalance i) / 2

where `P := Concrete.finitePathData hn hTail`. `hTail` is only needed to construct that existing record; the transition itself does not depend on `hTail`.

The imbalance expression agrees with `Concrete.localImbalance`: on a parent fibre of size `s`, `trueCount` is `Concrete.ones`, `falseCount` is `Concrete.zeros`, and `a-b = 2k-s` (whose square is `(s-2k)²`). On a singleton both sides return zero. This algebraic matching is also required as a Lean lemma.

## Sample nonemptiness

The baseline's `finiteAverage` requires `[Nonempty (Sample n m)]`. Supply it from an existing valid table under `m ≤ 2^n`; otherwise, no uniform sample distribution is defined. The partition recurrence itself does not require `J` nonempty and handles empty fibres.

## Merge plan

1. P0: compile and minimally repair the existing baseline, exposing finite averages where needed.
2. P1/P2: discharge the three compatibility lemmas above (parent fibre, child fibre, imbalance).
3. P10: add a concrete theorem `concrete_expectedExcess_succ`, using a double finite sum over `ValidTable n m × Fin m` and the partition recurrence. Wire it into `theorem_4_4_from_finite_paths` as `hTransition`.
4. Run `lake env lean P2_SizeRecurrence.lean` and then compile the integrated theorem in the pinned Lean+Mathlib environment.

The current file must **not** be reported as an unconditional proof of the concrete theorem before these steps succeed.

## Independent finite checks (not a Lean proof)

Run `python P2_verify.py` with Python 3. It uses exact rational arithmetic and enumerates:

- 55,987 one-step partition-and-branch assignments, for 0–6 columns and three parent labels;
- 10,668 greedy-path level checks on all injective ordered binary tables for 1–3 rows and up to 4 columns.

Both checks passed in the current environment. This checks the recurrence mathematics and the singleton convention, not elaboration/compilation of the Lean source or the concrete fibre identification.
