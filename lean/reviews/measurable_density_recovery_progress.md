# Measurable density and marked broadness recovery

`formalization/MeasurableDensityRecovery.lean` is complete: 23 theorems and 5 definitions, compiled with Lean 4.33.1 and the project's pinned mathlib. The importable `.olean` is available. The main `recover` theorem has only Lean/mathlib's standard axioms `propext`, `Classical.choice`, and `Quot.sound`; the source contains no `sorry`, `admit`, or custom axiom.

## Actual construction

The inputs are finite families of actual sets `O_i ⊆ Ref_i ⊆ Full_i`, positive parameters η and λ, finite full measures, measurable reference and output sets, the upper bound `ν.real Full_i ≤ 2λ`, and total retained mass `Σ ν.real O_i ≥ ηλM`. The general mass and marking arguments work for an arbitrary measure and measurable space; the direction and physical-ball results specialize to Euclidean tube families.

The good original indices are exactly those with `ν.real O_i ≥ ηλ/2`. They are reindexed by a genuine finite-set equivalence, and `Y_i` is the corresponding original output set. The mark is the actual measurable set

`G = (⋃ i, Y_i) ∩ {x : (η/8) m_Ref(x) ≤ m_Y(x)}`.

Finite integrability and the exact integral of multiplicity are proved through the existing actual indicator lemmas. No integrated loss bound, marked-mass bound, energy estimate, or good-index count is supplied as a hypothesis.

## Proven output

- The number of good tubes is at least `ηM/4`.
- Their total output mass is at least `ηλM/2`.
- Every selected output has measure in `[ηλ/2, 2λ]` and is measurable and finite.
- The constructed mark is measurable, finite, and contained in the selected union.
- At least half the selected total mass lies in the mark.
- Pointwise reference broadness with coefficient `K` transfers to the selected family on the mark with coefficient `K(8/η)`.
- Original full-shading physical-ball two-ends with coefficient `B` transfers to each full selected output with coefficient `B(4/η)` at the same radius range.
- Original direction separation and every actual real-m cap bound survive the good-index selection with unchanged parameters and cap coefficient.
- Positive original population and positive retained mass give a nonempty selected family.

The reference broadness input is deliberately a statement about `Ref`, not `O`. The proof injects selected-output cap incidences into original reference cap incidences and uses the constructed multiplicity ratio on `G`. This resolves the loss of pointwise broadness under arbitrary per-tube segment selection.

## Interface and exact scope

The combined theorem is `KakeyaFormal.MeasurableDensityRecovery.recover`. The definitions are `good`, `selectedIndex`, `selected`, `marked`, and `selectedFamily`. The latter retains actual original tubes and their independent finite-cell field. A caller selecting new unit segments should first supply the tube family made of those unit segments; broadness and cap transport then use their corresponding directions. The measurable selected outputs are passed separately, so no artificial cell enlargement is involved.

The proof does not need measurability of `Full`: finite measure, inclusions, the full upper bound, and the literal physical-ball inequalities suffice. This is a harmless generalization; reference and output measurability are required and all output measurability is established. It also requires only nonnegative bottom scale and coefficients, so the usual positive-scale applications are covered.

For the anisotropic application, take `Ref` to be exact normalized images and `O` to be the actual best-segment intersections supplied by `AnisotropicShading`; `AnisotropicTransport` supplies broadness and two-ends for the exact images. This module proves the density and mark restoration needed before invoking the actual hairbrush kernel. It does not claim the entire fractional seed, transformed-family assembly, or summation over all angular and spatial pieces by itself.

## Verification

Command, from `audit_work/formalization`:

`/Users/ssoh/.elan/bin/lake env lean -o .lake/build/lib/lean/MeasurableDensityRecovery.olean MeasurableDensityRecovery.lean`

The completed run returned exit status 0 without warnings. Component audits for `marked_mass_lower`, `selected_broad`, and `selected_two_ends`, and the final audit of `recover`, used only the standard axioms above. A source review confirmed the full/reference/output distinctions, positive η divisions, actual measure finiteness before `measureReal_mono`, exact bad/good mass partition, and unchanged direction indexing.
