# Authorized published inputs

The user explicitly authorized Katz–Tao and other published results as custom axioms, superseding the earlier no-custom-axioms preference. Exactly three are declared in [ExternalAxioms.lean](ExternalAxioms.lean) and hash-registered in [external_axioms.json](external_axioms.json). No novel manuscript result is axiomatized.

### KakeyaFormal.ExternalAxioms.wolff1995

Source: [Wolff (1995), Theorem 1, printed p. 652; includes the already known n=2 case described there.](https://ems.press/content/serial-article-files/37888?nt=1).

Formal statement: `∀ (n : ℕ), 2 ≤ n → NormalizedShadingBound n (((n : ℝ) + 2) / 2)`.

Trust boundary: Trusted normalized restricted-shading corollary of the cited published maximal estimate, including the mathematical translation from operator estimates via testing/Hölder and direction packing, fixed separation coefficients, projective versus angular metrics, closed capsule versus cylinder carriers, tube-volume normalization, and extension to 0<delta<=1. These source-to-predicate translations are assumed rather than kernel-proved here. The inverse-cap-coefficient weakening and measurable-to-grid adapter are proved. No fractional-cap, larger-ambient or manuscript generalized pivot result is assumed.

### KakeyaFormal.ExternalAxioms.katzTao2002

Source: [Katz–Tao, New bounds for Kakeya problems, arXiv:math/0102135v1 (16 February 2001), Theorem 1.1 and Section 5; journal publication 2002.](https://arxiv.org/pdf/math/0102135v1).

Formal statement: `∀ (n : ℕ), 2 ≤ n → NormalizedShadingBound n ((4 * (n : ℝ) + 3) / 7)`.

Trust boundary: Trusted normalized restricted-shading corollary of the cited published maximal estimate, including the mathematical translation from operator estimates via testing/Hölder and direction packing, fixed separation coefficients, projective versus angular metrics, closed capsule versus cylinder carriers, tube-volume normalization, and extension to 0<delta<=1. These source-to-predicate translations are assumed rather than kernel-proved here. The inverse-cap-coefficient weakening and measurable-to-grid adapter are proved. No fractional-cap, larger-ambient or manuscript generalized pivot result is assumed.

### KakeyaFormal.ExternalAxioms.zahl2021

Source: [Zahl, New Kakeya estimates using Gromov’s algebraic lemma, arXiv:1908.05314v4 (12 January 2021), Theorem 1.5, equation (1.6).](https://arxiv.org/pdf/1908.05314v4).

Formal statement: `∀ (n : ℕ), 2 ≤ n → NormalizedShadingBound n (zahlExponent n)`.

Trust boundary: Trusted normalized restricted-shading corollary of the cited published maximal estimate, including the mathematical translation from operator estimates via testing/Hölder and direction packing, fixed separation coefficients, projective versus angular metrics, closed capsule versus cylinder carriers, tube-volume normalization, and extension to 0<delta<=1. These source-to-predicate translations are assumed rather than kernel-proved here. The inverse-cap-coefficient weakening and measurable-to-grid adapter are proved. No fractional-cap, larger-ambient or manuscript generalized pivot result is assumed.


## All dependent declarations

The full audit reports7 dependent theorem declarations and10 dependent declarations in total, all within ExternalAxioms. MainMaximal, MainOperator and all46 new modules since checkpoint21 use only `propext`, `Classical.choice`, `Quot.sound`, or a subset. The generic normalized-shading adapter itself has an explicit premise and no custom dependency.

| Declaration | Registered dependency |
|---|---|
| `KakeyaFormal.ExternalAxioms.wolff_six` | `KakeyaFormal.ExternalAxioms.wolff1995` |
| `KakeyaFormal.ExternalAxioms.zahl_eight` | `KakeyaFormal.ExternalAxioms.zahl2021` |
| `KakeyaFormal.ExternalAxioms.katz_tao_discrete` | `KakeyaFormal.ExternalAxioms.katzTao2002` |
| `KakeyaFormal.ExternalAxioms.wolff_five` | `KakeyaFormal.ExternalAxioms.wolff1995` |
| `KakeyaFormal.ExternalAxioms.katz_tao_nine` | `KakeyaFormal.ExternalAxioms.katzTao2002` |
| `KakeyaFormal.ExternalAxioms.zahl_discrete` | `KakeyaFormal.ExternalAxioms.zahl2021` |
| `KakeyaFormal.ExternalAxioms.wolff_discrete` | `KakeyaFormal.ExternalAxioms.wolff1995` |
| `KakeyaFormal.ExternalAxioms.zahl2021` | `KakeyaFormal.ExternalAxioms.zahl2021` |
| `KakeyaFormal.ExternalAxioms.wolff1995` | `KakeyaFormal.ExternalAxioms.wolff1995` |
| `KakeyaFormal.ExternalAxioms.katzTao2002` | `KakeyaFormal.ExternalAxioms.katzTao2002` |

See the [statement review](reviews/external_axiom_statement_review.md), [verifier review](reviews/external_axiom_verifier_review.md) and [complete dependency inventory](verification/summary.json). The exact source translations above are trusted assumptions; the subsequent adapters are proved. Katz–Tao's saturated recursion is not silently assumed for arbitrary-density novel inputs. The strict `--reject-external-axioms` option rejects the registered package by design.
