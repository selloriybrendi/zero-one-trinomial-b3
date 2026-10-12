# The trinomials 1 + a x^3 + x^k are not unfair factors of 0–1 polynomials

Code, certificates, logs and Lean sources for the paper by **Otakhon U. Kenjaev**
(ORCID [0009-0009-3566-9285](https://orcid.org/0009-0009-3566-9285)) — see `paper/`.

**Theorem.** For every k ≥ 4 with 3 ∤ k and every 0 < a < 1, the trinomial
1 + a x³ + x^k does not divide any 0–1 polynomial with a nonzero cofactor having
nonnegative coefficients; by reciprocity the same holds for 1 + a x^(k−3) + x^k.
This is a special case of the *unfair 0–1 polynomial conjecture*
([MathOverflow 339137](https://mathoverflow.net/q/339137)); the general conjecture remains open.

| Part of the proof | How to re-check | Log |
|---|---|---|
| 1/2 < a < 1 (hand proof, partly in Lean 4) | `cd lean/Trinom && lake build` | — |
| 0 < a ≤ 1/2, k ≥ 67 (uniform certificate) | `python retsenziya/uniform_sertifikat.py 67 60` and `... 151 60` | `retsenziya/uniform_sertifikat_k67.log`, `_k151.log` |
| class formula check | `python retsenziya/oyna_formula.py 4 120` | — |
| k ≤ 60 | `GCD_TEKSHIR=1 python simvolik_isbot_flint.py 3 k 2000` (driver `retsenziya/toliq_census.sh`) | `retsenziya/toliq_census.log` |
| 61 ≤ k ≤ 149 | `GCD_TEKSHIR=1 python simvolik_isbot_flint.py 3 k 4000` (driver `retsenziya/b3_61_150.sh`) | `retsenziya/b3_61_150.log` |
| root points 151 ≤ k ≤ 250 | `python retsenziya/ildiz_nuqta.py k` (driver `retsenziya/ildiz_nuqta.sh`) | `retsenziya/ildiz_nuqta.log` |

Requirements: Python 3, [python-flint](https://pypi.org/project/python-flint/) 0.9.0, cypari2 (PARI/GP 2.17.2);
Lean 4 v4.34.1 with Mathlib. Every certificate run recomputes its verdict and reads no stored data;
the logs are for comparison only. Runs were made on an Apple M5 (10 cores, 16 GB).

Use of AI tools: the AI assistant Claude (Anthropic) was used to write and run the scripts, draft the
Lean formalisation and draft the paper; see the paper's section *Use of AI tools*.

License: code MIT (see `LICENSE`); paper CC BY 4.0.
