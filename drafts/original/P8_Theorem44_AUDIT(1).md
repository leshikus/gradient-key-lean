# P8 — Theorem 4.4 deterministic audit

## Delivered artifacts

- `P8_Theorem44.lean`: standalone 693-line Mathlib module, namespace `P8Theorem44`, no baseline import; conditional full theorem with the explicit bound and strict corollaries (a)–(c).
- `P8_theorem44_numeric_audit.py`: reproducible numerical spot checks (not a proof).
- `P8_Theorem44.compile.log`: compilation invocation failure.

The Lean module is a namespace-isolated adaptation of the deterministic portion of the candidate baseline, with an independent scaled-recurrence/telescoping proof replacing its weighted recurrence proof. It does **not** claim to formalize or discharge the conditional probability bounds of Lemmas 4.1 and 4.3.

## Source

`article(9).tex`, Section 4, Lemmas 4.1–4.3 and Theorem 4.4 (lines 341–458). The Library copy of `GradientKeySection4.lean` supplied the preexisting candidate theorem interface. The separately mentioned `GradientKeySection4_STATUS.md` could not be located. No source-wide edits were made.

## Mathematical audit and dependencies

The *precise* recurrence from Lemma 4.1 is

    e_(i+1) = (e_i - p_i + V_i)/2,   e_0 = m-1,
    t ≤ Σ_{i<h} p_i + e_h.

Multiplication by 2^(i+1) telescopes, giving

    2^h e_h = m-1 + Σ_{i<h} 2^i (V_i-p_i).

Thus

    t ≤ (m-1)/2^h + Σ_{i<h}(1-2^(i-h))p_i
                  + Σ_{i<h}2^(i-h)V_i.

With p_i ≤ 1, the first two terms are at most h-1+m/2^h.

For h = ell = Nat.log 2 m, the assumptions 2≤m≤2^n yield 1≤ell≤n, so n-i≥1 for i<ell. Lemma 4.3's **two** bounds are taken directly:

    V_i ≤ n/(n-i),
    V_i ≤ 2 p_i (1+ln(2n/((n-i)p_i)))  when p_i>0.

If p_i=0, V_i=0 because v_i is defined to be 0 off forks. For c=2n/(n-i)≥2, the inequality ln(1/p)≤1/p-1 on 0<p≤1 implies

    p(1+ln(c/p)) ≤ 1+ln c.

This proves the pointwise minimum used in the theorem **without introducing a new concentration estimate**. The explicit `hVZero` argument of the generic Lean theorem remains a bridge obligation: its concrete proof must use the definition of the probability/expectation, not an added assumption.

For x=m/2^ell in [1,2), concavity gives x-1≤log₂ x, hence

    ell-1+m/2^ell ≤ log₂ m.

This includes endpoints m=2 and every power of two. The geometric sum

    Σ_{i<ell}2^(i-ell) = 1 - 2^(-ell) < 1

is the source of **strict** inequalities (a) and (b), since their coefficients are positive. (c) follows from (b) once

    2*ell-2 ≤ n  ↔  2*ell ≤ n+2,

which the Lean candidate handles with `omega`, avoiding a potentially unsafe reinterpretation of `Nat.sub` as integer subtraction.

## Lean declarations and actual status

- `scaled_recurrence_identity`: independent unrolling of Lemma 4.1 — **NOT COMPILED**.
- `uniform_bound_from_lemmas`: pointwise weighted uniform bound from recurrence — **NOT COMPILED**.
- `theorem_4_4_main`: paper's displayed sum assuming the combined row bound — **NOT COMPILED**.
- `entropy_log_bound` and `imbalance_of_lemma_4_3`: passage from original two Lemma 4.3 bounds to the combined row bound — **NOT COMPILED**.
- `binary_window_chord`, `nat_log_pos_and_le`: logarithmic and row-count arithmetic — **NOT COMPILED**.
- `theorem_4_4_a_nat`, `theorem_4_4_b_nat`, `theorem_4_4_c_nat`: strict natural-log corollaries with `ell=Nat.log 2 m` — **NOT COMPILED**.
- `theorem_4_4_all_from_probabilistic_lemmas`: one combined interface taking original recurrence, tail, probabilities and **two** Lemma 4.3 estimates, returning the main inequality and (a)–(c) — **NOT COMPILED**.

No source-level `sorry`, `admit`, `axiom`, or `unsafe` constructs are introduced. These are candidate proof scripts; no Lean kernel has checked them.

Attempted command:

    cd /mnt/data && lake env lean P8_Theorem44.lean

Actual result: **exit 127**; `bash: line 1: lake: command not found`. No Lean toolchain or Mathlib project was installed, and no exact pinned revision can be reported. These are **environment/toolchain errors**, not evidence that the proof type-checks or fails to type-check.

The separate Python check ran **57,100 parameter trials** for 1≤n≤20, including m=2 and power-of-two endpoints, and reported PASS. It checks the mathematical inequalities under sampled abstract parameter values but does not provide formal verification.

## Minimal merge plan

1. In a pinned Lean 4 + Mathlib repository, add `P8_Theorem44.lean` without replacing the baseline and run `lake env lean P8_Theorem44.lean`.
2. Fix any actual elaboration/tactic errors reported by the compiler in this separate file; re-run until the command returns exit 0. Do not infer compilation from the lack of `sorry`.
3. Supply the five concrete interfaces (`hInit`, `hRec`, `hTail`, `0≤p≤1`, `p=0→V=0`) from the finite greedy-path model and the two row imbalance bounds (`hVMean`, `hVTail`) from Lemma 4.3. The latter **remain other agents' obligations**; none may be postulated as a new global axiom.
4. Invoke `P8Theorem44.theorem_4_4_all_from_probabilistic_lemmas` with the concrete expected depth, expected excess, fork probabilities, and expected imbalance. Check the resulting statement against Section 4 again after integration.

**Scope:** Only the deterministic conclusion was addressed. The full greedy theorem awaits the concrete probability bridges and compiler verification.
