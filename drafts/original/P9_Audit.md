# P9 — Adversarial audit of Section 4 and `GradientKeySection4.lean` v4

**Status: MATHEMATICAL SPOT CHECKS PASSED; LEAN NOT COMPILED; THEOREM 4.4 NOT YET FORMALIZED UNCONDITIONALLY.**

Scope: Section 4 of the supplied `article(10).tex` (lines 341–460); indexed project copy of `GradientKeySection4.lean` v4 (1,735 lines, inspected by file reads); assignment `P9_adversarial_audit.md`. The requested `GradientKeySection4_STATUS.md` and `verify_row_deletion.py` were **not available** in the accessible project/conversation/library search; the Lean source was available for reading but not for raw-byte materialization. I created an independent exhaustive Python test instead. No changes were made to the paper or baseline.

## Ranked findings

### P9-01 — Confirmed source-level type mismatch in `partner_twice`

- **Rank:** High; **compilation blocker** (static type mismatch, not a captured compiler diagnostic).
- **Source:** `GradientKeySection4.lean`, near lines 1454–1470, the first branch of `rcases hthree` in `RowDeletion.partner_twice`.
- **Problem:** `hneq` has type `partner B a ≠ a`; the first branch `hba` has type `partner B a = a`. Current code says `hneq hba.symm`, which supplies `a = partner B a` instead of the expected equality. Equality is not automatically reversed when passed to `Ne`.
- **Smallest local correction:** Replace `exact False.elim (hneq hba.symm)` by `exact False.elim (hneq hba)`. Leave the next branch's `hneq2 hbc.symm` and the last branch's `hac.symm` unchanged; their orientations are appropriate. See `P9_patch.diff`.
- **Impact:** `partner_twice` is used by `duplicate_sign_sum_zero` → `all_signs_eq_unique_signs` → `conditional_inserted_imbalance_exact`, so the source-level defect blocks the exact-moment chain unless corrected. This one-line change is necessary, **not a claim that it suffices for compilation**.

### P9-02 — Real theorem statement remains conditional, not a proof of `t_{n,m}(G)`

- **Rank:** High; **unproved mathematical-to-model bridge** (not an error in the paper).
- **Source:** Lean lines 190–210, 550–684, 760–890, 1027–1086, 1667–1735.
- **Details:** `theorem_4_4_main` takes arbitrary real `t`, functions `e,p,V`, and hypotheses `hInit`, `hRec`, `hTail`, `hProb`, and `hV`. The packaged theorem assumes the two nontrivial Lemma 4.3 bounds. `theorem_4_4_from_finite_paths` still assumes `hTransition`, `hVMean`, and `hVTail`, while `Concrete.finitePathData` requires an external pointwise `hTail`. No end-to-end declaration instantiates these for `Concrete.Sample n m`, discharges the row-deletion bounds, and identifies `P.expectedDepth` with the paper's `t_{n,m}(G)`.
- **Why it matters:** These assumptions encode the key probabilistic substance; a proof using them is legitimately a conditional theorem, but not a complete formal proof of the published unconditional statement. This is disclosed in the Lean file's header, so it is not evidence of intentional concealment.
- **Local action:** Keep conditional theorems clearly labelled. Integrate the path invariant, transition, row-deletion conditional law, Hoeffding tail, Lemma 4.3 bounds, sample nonemptiness and average-cost identification into a *new* concrete corollary. Do not state that the original Theorem 4.4 is closed before the corollary compiles without extra probabilistic hypotheses.

### P9-03 — `pathDepth` overcounts tests on matrices with duplicate columns

- **Rank:** Medium; **model-scope mismatch**, not a flaw for `ValidTable`.
- **Source:** Lean lines 1014–1059, particularly `candidateStep` and `pathDepth`. Paper lines 380–384.
- **Smallest counterexample:** One row, two identical all-zero columns (`n=1`, `m=2` but *not* `DistinctColumns`). `candidateStep` leaves the two-column set unchanged because all row qualities are zero, while `pathDepth` counts the non-singleton candidate set at depth `0` and returns `1`. The paper's `G(B)` is a terminal leaf with **zero tests**.
- **Impact:** The current concrete sampled cost is used only for distinct-column tables (`ValidTable`), where the issue does not arise. **Do not** reuse `pathDepth` for row-deleted `B` without a guard.
- **Local action:** Preserve `pathDepth` for valid tables with an explicit distinctness argument, and if necessary introduce a separate deleted-tree depth counting only actual positive-quality forks. The row-deleted *candidate sets* can still be used (they remain constant after termination), as in the paper.

### P9-04 — Row-deletion probability-law bridge absent

- **Rank:** High; **incomplete formal integration**, not a mathematical counterexample.
- **Source:** Lean lines 912–960, 1248–1369, 1627–1657; paper lines 386–406.
- **Finding:** `Extension B = {x // ValidExtension B x}` correctly characterizes inserted rows restoring distinctness. `[Nonempty (Extension B)]` correctly restricts the exact-moment proof to realizable deleted tables. But the Lean file has not proved that conditioning **the concrete uniform sample** on `deleteRow A r = B` and `j=j₀` produces the uniform measure on `Extension B`, nor established a concrete `Fin n` row-removal map preserving the order of surviving rows. The fixed `j₀` does **not** introduce bias mathematically, since `j` is sampled independently and uniformly, but the identification must be proved in Lean.
- **Local action:** Provide a measure-preserving bijection `A ↔ x : Extension B` for fixed `B,r`, then show that conditioning additionally on `j=j₀` leaves the extension weights unchanged. Link the `PairClosed` property of actual deleted-tree candidate sets before using the exact-moment theorem.

### P9-05 — No exact pinned toolchain or executable compilation result

- **Rank:** High; **verification blocker**.
- **Observed command:** `lake env lean GradientKeySection4.lean` → exit code `127`, `bash: line 1: lake: command not found`. No `lean` executable or pinned Mathlib checkout was present locally. Moreover, the indexed project Lean source could be read but not materialized as original bytes.
- **Consequence:** **NOT COMPILED.** The file's absence of `sorry`, `admit`, or `axiom` in declarative proof bodies does not certify compilation, and API/tactic compatibility of the remainder is still unknown. The source-level `P9-01` mismatch is a reason to expect at least one failure if compiled.
- **Local action:** Pin `lean-toolchain` and `lake-manifest.json`; run `lake env lean GradientKeySection4.lean` and the focused exact-moment module. Preserve full diagnostic output and patch only failures confirmed in that environment. Check imported helper names, `private` declaration accessibility, and all tactic steps after the first failure is fixed; no other specific API error is claimed without a compiler run.

## Checks that did *not* reveal a defect

1. **First maximum and tie-breaking:** `Concrete.greedyRow = (List.argmax (quality A S) (List.finRange n)).getD ...` has the intended row order for `n>0`. Lean/Mathlib docs say `List.finRange n` lists `0,...,n-1` in order and `List.argmax` retains the **first** maximum, including ties. For `n=2`, columns `00` and `11`, both row qualities are `1`; row `0` is chosen. Sources: https://leanprover-community.github.io/mathlib4_docs/Mathlib/Data/List/MinMax.html ; https://lean-lang.org/doc/api/Init/Data/List/FinRange.html . The API behavior was inspected, **not compiled** against the candidate's unpinned dependency version.

2. **All-row selection and reuse:** On a distinct-column table, every non-singleton candidate set contains two columns differing in some row, so maximal quality is positive. Once a row is tested, it is constant on every descendant candidate set; its later quality is zero. Hence allowing all rows in `List.finRange n` does not cause reuse along a genuine path. Still needs a Lean invariant/proof.

3. **Deleted-tree termination and equality-class closure:** Deleted matrices can have duplicate columns and may terminate at a non-singleton leaf; e.g., deleting the sole row of a `1 × 2` distinct-column table leaves two identical empty column vectors. This is explicitly allowed by the paper. `PairClosed B S` remains true: equal columns have equal bits in every surviving row, so each split keeps them together, and terminal sets are constant.

4. **Prefix coupling requires preserving row order:** For columns `(000,010,100)` in a 3-row table (bits listed as row-0, row-1, row-2), rows 0 and 1 tie with quality 1, while row 2 is constant. Deleting unused row 2 **without reordering** leaves row 0 chosen; for column `j=0`, `S₁={0,1}` in both paths. Reversing the remaining two rows makes the tie choose old row 1 and gives `{0,2}` instead. The paper explicitly retains order. A concrete row-deletion constructor must do likewise.

5. **Conditional mean and sign convention:** For a deleted matrix with equality classes `{0,1}` and `{2}`, and `S={0,1,2}`, there are four valid inserted rows. Each pair contributes one 1; the remaining bit is fair, so the squared imbalance is `1/3` for every extension. `f/s=1/3` agrees. `signedBit` uses `+1` for a one, yielding `2k-s` rather than the paper's `s-2k`, but the square is unchanged. No sign error found in the identity. The exact theorem allows `S=∅` and relies on Lean's `0/0=0`; the paper states `S` nonempty. This is a benign algebraic extension, not a valid probabilistic conditioning state for the intended lemma.

6. **Natural/real denominators and boundaries:** Under `2≤m≤2^n`, necessarily `n≥1` and `1≤ell=Nat.log 2 m≤n`. For `i<ell`, the crucial `n-i≥1`; `S_i` on a sampled path contains `j` and hence has `card≥1`; valid `Sample n m` and realizable `Extension B` are nonempty. No zero-denominator counterexample found on the intended domain. Without those hypotheses, `imbalanceBound n i` is just an algebraic expression involving potentially zero denominators, so do not apply the estimates off-domain. The `n=ell` and `m=2` cases were included in the exhaustive checks.

7. **Expected depth vs paper's average:** `Sample n m = ValidTable n m × Fin m`, a uniform finite product. Thus its expectation of `pathDepth` equals `1/|A_{n,m}| · Σ_A (1/m) · Σ_j L_j`, matching `t_{n,m}(G)`, provided `pathDepth=L_j` is proved on valid tables. No reweighting issue was detected; the *formal equality* is still absent.

8. **Unproved assumptions, private names, shadowing:** The unproved probabilistic assumptions are explicit parameters (see P9-02/P9-04), not `axiom` declarations. The first visible type-direction mismatch is P9-01. `private` helpers such as `finiteAverage` are reused in later namespaces in the same file; their cross-namespace accessibility needs compiler confirmation, but there is no evidence of an actual inaccessible-name error. Nothing in the read source establishes malicious shadowing or a silently changed mathematical target, beyond the disclosed conditionalization.

## Independent exhaustive check

The attached script `P9_verify.py` uses exact `fractions.Fraction` for combinatorial expectations, ordinary Python for the finite greedy trees, and floating-point checks for inequalities involving logarithms. It does **not** execute Lean. It examines every unordered set of distinct binary column vectors for `1≤n≤4`, `2≤m≤min(2^n,5)`, and every selected column. Column permutations yield the same costs and properties after relabelling, so this covers the corresponding labelled uniform distributions for these tests.

```text
12 (n,m) models; 31,854 table-column representatives
71,842 original fork states
126,570 row-deletion paths; 236,422 prefix-coupling cases
232 distinct realizable deleted tables (n≤3,m≤5)
2,014 PairClosed candidate subsets (including 232 empty cases)
1,782 nonempty PairClosed candidate subsets
No failed checks for: tie selection, no reuse, deleted-tree PairClosed,
order-preserving prefix coupling, exact conditional moment,
path-size recurrence, expected-tail inequality,
Lemma 4.3 mean/tail bounds, or Theorem 4.4 displayed/(a)/(b)/(c) bounds.
```

Illustrative exact average costs: `t_(2,3)=5/3`, `t_(3,4)=71/35`, `t_(4,4)=921/455`, `t_(4,5)=3278/1365`. These are **independent numerical checks**, not proofs for arbitrary parameters. Reproduce with `python P9_verify.py`.

## Theorem declarations and status

| Declaration | Mathematical scope | Status |
| --- | --- | --- |
| `Concrete.greedyRow`, `candidateAt`, `pathDepth` | Concrete finite greedy sampling | Definitions inspected; NOT COMPILED; path-depth caveat for duplicate tables |
| `RowDeletion.no_three_equal_columns`, `validExtension_iff` | Structural deleted-row facts | Mathematically sound by argument; NOT COMPILED |
| `RowDeletion.conditional_inserted_imbalance_exact` | Exact uniform-extension moment | Exhaustively checked for small cases; blocked by upstream source-level issue; NOT COMPILED |
| `mean_imbalance_from_unused_rows` | Conditional finite averaging lemma | Pure implication with `hCompare`/`hRowMean` assumptions; NOT COMPILED |
| `theorem_4_4_main`, `_a_nat`, `_b_nat`, `_c_nat` | Main bound and corollaries | Conditional on `hRec`, `hTail`, `hV`; NOT COMPILED |
| `theorem_4_4_from_finite_paths` | Theorem 4.4 for abstract finite paths | Still conditional on `hTransition`, `hVMean`, `hVTail`; NOT COMPILED |
| Unconditional `t_{n,m}(G)` theorem | Paper's exact Theorem 4.4 | **NOT PRESENT / NOT PROVED** |

## Dependencies and minimal merge plan

1. Apply **only** the one-line `P9_patch.diff` correction to the shared Lean baseline, once source ownership allows; keep P9 files separate. Obtain an actual pinned Lean/Mathlib compilation log before declaring progress.
2. Require the greedy-invariants agent to prove positive splitting, row non-reuse, exact path depth, candidate-set persistence and pointwise tail. The row-deletion/coupling agent must provide an order-preserving deletion map and `PairClosed` invariant. The conditional-uniform agent must connect concrete sampled conditional probabilities to `Extension B`.
3. Integrate the independent Lemma 4.1 transition and the mean plus Hoeffding-tail halves of Lemma 4.3. Do not accidentally use the stronger *exact moment* statement as a replacement for the absent tail estimate.
4. Identify the finite product average with the article's `t_{n,m}(G)` and prove `Nonempty (Sample n m)` from `2≤m≤2^n`. Only then package the already-conditional Theorem 4.4 algebra into an unconditional concrete theorem.
5. Run `lake env lean` on a pinned toolchain, review exported declaration types with `#check`/`#print`, check there is no imported extra assumption, and rerun `python P9_verify.py`. Avoid unrelated changes to the paper.

**Conclusion:** No counterexample to the Section 4 mathematics was found. The current Lean candidate has at least one source-level proof defect, an explicitly unfinished probability interface, and no real compiler verification. Those issues should be fixed locally before anyone calls Theorem 4.4 formally proved.
