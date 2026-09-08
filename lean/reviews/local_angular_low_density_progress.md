# Actual local angular low-density case

Two new modules are complete, frozen, clean-built, and audited from their exact source:

- `LocalAngularLowDensity.lean`: seven theorems;
- `LocalAngularLowDensityOriginal.lean`: one theorem.

Both exact-source axiom audits contain only `propext`, `Classical.choice`, and `Quot.sound`. There are no custom analytic axioms, `sorry`, `admit`, warnings, or compiler errors. Their built `.olean` files are ready for downstream imports.

## Final original-parameter statement

`LocalAngularLowDensityOriginal.original_parameters` proves the Section 7 case-2 estimate, in ambient dimension `k+2`:

`c * A^(-1) * (δ/τ)^(m-D+ε) * λold^C * Mbox ≤ #S`.

The constant c is positive and chosen before all actual tube families, measurable sets, scales, original and retained densities, populations, cap coefficients, support cells, and retained outputs. It depends only on the fixed dimension/aperture, two-ends and broadness exponents, fixed logarithmic budget coefficients/exponents, the fixed coarse-complement exponent a, the target exponents, and ε.

The assumptions are concrete original-box data: actual measurable nested Full/Ref, Full contained in the original radius-δ tube carriers, original δ-separated directions, actual real m-cap bound, angular aperture `angular*τ`, per-tube full upper mass `2 λold δ^(k+1)`, original total marked mass `η λold δ^(k+1) Mbox`, pointwise Ref broadness, original full two ends, and literal original support

`union Full ⊆ normalizedSet W (cellUnion δ S)`, with W≥1.

The SAME actual `AnisotropicSamplingRetention.Output` is supplied on these original Full sets. Its sparse alternative is `Output.density ≤ (δ/τ)^(1/3)`. All conditioning bounds are stated with the original natural logarithm `log(2/δ)`: upper budgets for B and K, lower budgets for the original marked fraction η and actual effective retention e. The exponents of these polynomial logarithms are explicitly nonnegative.

The only scale-case relation is the actual coarse-complement test `(δ/τ)^a ≤ δ` for fixed a≥1. The theorem applies at every `0<δ≤τ≤1`; it introduces no additional small-scale cutoff. The target margin is explicit:

`(m+3)/2 - D + (C-2)/3 > 0`,

with C≥2 and ε>0. The preceding retained-parameter theorem allows ε≥0 and concludes the same bound using `Output.density^C * Output.N`.

## Actual proof chain

1. `AngularBoxLogLoss.single_box_logarithmic` is applied to the ORIGINAL actual Full/Ref box data. It constructs its own legal segment, separation color, measurable recovery, and hairbrush; the final theorem assumes none of those choices or the hairbrush inequality.
2. `volume_to_old_cells` uses exact half-open-grid volume `δ^(k+2)*#S/W^(k+2)` and the literal support inclusion. It cancels the common δ volume factor and weakens the favorable `δ≤δ/τ` inequality. Thus the result is a lower bound for old cells, never an identification of old count with transformed normalized volume. The favorable W and τ factors can safely be discarded.
3. The hairbrush prefactor's A dependence is proved to be A^(-1/2), then weakened uniformly to A^(-1) for A≥1. c is independent of A.
4. The SAME retained output has an injective map into the original box and a density at most λold. These actual fields prove `Output.density^2 * Output.N ≤ λold^2 * Mbox`; no retained population comparison is assumed.
5. The sparse cutoff gives the exact power comparison with positive margin above. Fixed logarithmic conditioning is transported across the explicit coarse-complement test and absorbed by `PivotLossAbsorption.inverse_log_delta`. Natural-log budgets are converted internally to the existing `seedLog δ` hairbrush interface.
6. For the original-parameter corollary, the geometric bound uses ε/2. `AnisotropicDensityPower.output_power` derives actual density-power/population retention from the same Output. A second inverse-log absorption uses ε/2. Using the original `seedLog δ≥1` internally avoids a spurious requirement `log(2/(δ/τ))≥1`; the outer hypotheses remain native original natural-log budgets.

The scalar helper `uniform_sparse` isolates exponent algebra, but the final geometric statements do not take that helper's lower-bound premise: they derive it by the actual hairbrush and exact support geometry.

## Application boundary

`AngularSpatialSampling` now supplies the actual Full/Ref, common map, output, and old support for each good spatial box. It must instantiate the physical density as `V.density/W^(k+1)` and use its explicit width-power test to obtain density≤1. The old reference depth and new measured selection depth remain separate. Global assembly still needs to derive common fixed original-log budgets across these boxes, apply the correct coarse/low/high alternative, and sum only the original old-cell counts with the proved angular/spatial overlap. This module does not claim that global summation has already been performed.

Source hashes:

- LocalAngularLowDensity: `34541e9633172250aff74565c74f2014d282997b363979fd21485d1412eb32a9`.
- LocalAngularLowDensityOriginal: `7b9a172ee758ab271aacf896df70a2b554ad592a0336c7bc007ee22df750b8d1`.

Exact-source audits: `LocalAngularLowDensitySourceAudit.lean`, `LocalAngularLowDensityOriginalSourceAudit.lean`; logs in `audit_work/LocalAngularLowDensity_axioms.log` and `audit_work/LocalAngularLowDensityOriginal_axioms.log`.
