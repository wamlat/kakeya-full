# Six-dimensional marked core

New development module `formalization/SixDimensionalCore.lean`, outside frozen checkpoint 14. No registry, lakefile, verifier or dependency was edited.

Four explicit theorems:

1. `base`: `DiscreteEstimate 6 5 4 4`, derived from the proved `FractionalSeed.fractional_discrete_seed`.
2. `lift`: `DiscreteEstimate 7 4 (7/2) (7/2)`, derived from the same proved fractional seed in the actual lifted ambient dimension seven.
3. `marked_estimate`: exact specialization of `MarkedPivotEstimate.all_scales`, with one positive constant fixed before all actual configurations:

   `c*A⁻¹*δ^(7/8+eps)*lam^(15/4)*M ≤ E.card`.

   Here `D=33/8`, `C=15/4`, and `5-D=7/8`. No analytic base or lifted estimate is left as a caller hypothesis.
4. `marked_union_estimate`: the same conclusion for the actual occupied full union `F.unionCells`.

The hypotheses remain precisely visible through `OriginalPivotSlabs.Hypotheses`: an actual six-dimensional tube/grid family with δ>0 and δ≤1; δ-separated directions, cap-five coefficient A≥1, fixed width/base normalization; full shadings with counts between lam/δ and 2lam/δ; actual marked subsets with total count at least xi*lam*M/δ and one-tenth angular broadness at radius theta; full-shading two ends with exponent alpha>0; fixed upper logarithmic budgets for B and theta⁻¹, and a lower logarithmic budget for xi. The family is nonempty, and lam,xi≤1. Width≥1/12 is explicit. All conditioning budget constants and exponents precede the family and its varying scale, density, cap coefficient and marks.

This is a standard-foundations-only marked theorem. It imports `FractionalSeed` and `MarkedPivotEstimate`, not `ExternalAxioms`; no published-result axiom is needed to supply either seed. The lift is in R7, not R8. The statement does not claim the unrestricted measurable implication M6(4) -> M6(33/8): angular globalization and two-ends removal, followed by the actual measurable/global-normalization interface, remain outside this module. In particular the density exponent here is 15/4, under stronger marked/two-ends hypotheses; it has not been relabeled as the unrestricted density exponent 33/8.

Verification: clean Lean 4.33.1 build and `.olean` generation, no warnings or diagnostics; fresh exact-source-prefix axiom audit of all four local theorems. Every result depends only on `propext`, `Classical.choice`, `Quot.sound`. Audit artifacts: `six_dimensional_core_full_source_audit.lean` and `.log`; clean build log: `six_dimensional_core_compile.log`. Source SHA-256: `b37e9ee19d97d10e487534d25df89c00d5f71432b0fb5e1b4599d7cdc19c4db7`.
