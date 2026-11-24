# Upper-level review of *The gradient key on random tables*: is everything up to date?

You are a referee for a combinatorics/probability journal (target: Random Structures & Algorithms) and a Lean 4
reader. Review the article as a whole and check that the article, the code/data repository and the Lean
repository agree. Report findings; do not edit any repository unless the authors ask.

## Sources (read the current `main` of each on GitHub)

- Article: https://github.com/leshikus/gradient-key — `article.tex` (with `small_formulas.tex`,
  `small_table_m.tex`, `small_table_n.tex`, `constants.tex`, `refs.bib`) and `article.pdf`.
  Last article commit: https://github.com/leshikus/gradient-key/commit/1b72d11
- Code and data: https://github.com/leshikus/gradient-key-impl — the article cites
  https://github.com/leshikus/gradient-key-impl/tree/38a3ce4; `main` is at
  https://github.com/leshikus/gradient-key-impl/commit/417c2c1 (one commit later: `data/small/exact_values.md`
  drops the "both engines" column). Data: `data/small/` (`exact_values.md`, `formulas.md`, `fixed_n.csv`),
  `data/gradient-bound/` (`exact.csv`, `exact_formula.csv`, `exact_complement.csv`).
- Lean: https://github.com/leshikus/gradient-key-lean — the article cites
  https://github.com/leshikus/gradient-key-lean/tree/aa1652f (CI green:
  https://github.com/leshikus/gradient-key-lean/actions/runs/45450295892). Status map: `FORMALIZATION_STATUS.md`;
  theorem checks: `Section3/Check3.lean`, `Section4/Check.lean`, `ci/expected_theorems.txt`; CI runs:
  https://github.com/leshikus/gradient-key-lean/actions

If a repository is private or unreachable, say so and review only what you can read; do not guess its contents.

The authors check the proofs themselves (Fedotov is an author). Do not report "proofs not checked by a
mathematician"; report concrete gaps or errors instead.

## 1. Is everything up to date?

1. Commit citations. List every commit hash and URL in `article.tex` (Sections 3.4, 4 and Data availability).
   For each, say whether it is the current `main` and whether the newer commits change anything the article
   states. Recommend one impl commit and one Lean commit to cite.
2. Lean claims. For every sentence of the article that says Lean proves something, give the declaration and
   module from `FORMALIZATION_STATUS.md`, and confirm that it is in `Check3.lean`/`Check.lean` and
   `ci/expected_theorems.txt`, and that CI passed at the cited commit. Flag claims the article attributes to
   Lean that Lean does not prove, and verified results the article does not mention.
3. Statement match. For each Lean-proved claim compare the Lean statement with the article: hypotheses
   (`0 < n`, `2 ≤ m ≤ 2^n`, `n ≥ 3`, …), definitions (`C(m)`, `t_{n,m}(G)`, `N_m(n)`, `B_k`, `a_j`, `M`, `J`,
   `L_max`, `⌈log m⌉`, missing words), and conclusions. Flag any weaker, stronger or different statement.
4. Data. Check that the numbers in the article match the repository files: Table 1 (`m`, terms, `J`, `A_m`,
   `r_m`) against `data/small/formulas.md`; Table 2 against `data/small/fixed_n.csv` and `exact_values.md`;
   the examples (`t_{3,4} = 3408/1680`, `t_{4,11} - C(11) = 1/3003`, `t_{4,10} - C(10) = 18/5005`,
   `t_{3,5} = C(5) < t_{4,5}`); the counts in the text (48 brute-force pairs, 120 pairs `n ≤ 6`, 41 analytic
   values, "near 10^10 at (8,32)"). Check that every file path named in the article exists at the cited commit.
5. README and status files. Check that `gradient-key-lean/README.md`, `FORMALIZATION_STATUS.md` ("Not
   formalized" paragraph) and `gradient-key-impl/README.md` describe the current state and agree with the article.

## 2. Upper-level review of the article

6. Results 1–4: are they stated once, precisely, and proved where announced? Is the contribution clear from the
   abstract and introduction alone?
7. Structure: order of sections, forward references, whether each section is needed for Results 1–4.
8. Proofs: give each gap or error with line number, the missing step, and a fix. Separate gaps in the article's
   proofs from gaps in the formalization.
9. Comparison with prior work (`refs.bib`): missing or misattributed references; do not invent attributions.

## 3. House rules to check (from `gradient-key/CLAUDE.md`)

- Every symbol, term and abbreviation defined at or before first use; the abstract stands alone.
- One term per object throughout (candidate set, fork, split imbalance, missing words, …).
- Sentences under about 30–35 words; no filler.
- Only what the article does and proves: no "we do not know", no negative or apologetic remarks, no unproved
  claims.
- No subjective words: simple, difficult, natural (except "natural logarithm"), much, quickly, very, easy, obvious,
  clearly, hard, complicated, trivial, straightforward.
- No data tables or long coefficient lists in the TeX; the article states ranges and links to the repository files.
- The "Use of AI tools" note is present.

## Output

One report, ordered by severity, in three groups:

1. **Out of date / inconsistent** (citations, Lean claims, data): location (file:line), what differs, the fix.
2. **Mathematics and structure**: location, issue, proposed text (shortened, following the house rules).
3. **Style**: location, rule broken, proposed text.

End with the list of changes the authors must decide on, and the list of changes that are mechanical
(e.g. updating a commit hash).
