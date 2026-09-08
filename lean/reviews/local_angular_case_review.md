# Independent review: the actual sparse-density angular case

Reviewed 2026-09-06. No mathematical defect was found in the reviewed versions of `LocalAngularLowDensity.lean` or `LocalAngularLowDensityOriginal.lean`. Both sources were read in full and independently recompiled with the matching project's `lake env lean <module>.lean`; both returned exit 0 with no diagnostics. No source was edited. This review complements, rather than replaces, the modules' separate full-source axiom audits.

| Source | Reviewed SHA-256 |
|---|---|
| `LocalAngularLowDensity.lean` | `34541e9633172250aff74565c74f2014d282997b363979fd21485d1412eb32a9` |
| `LocalAngularLowDensityOriginal.lean` | `7b9a172ee758ab271aacf896df70a2b554ad592a0336c7bc007ee22df750b8d1` |

Relevant interfaces checked included `AngularBoxLogLoss.single_box_logarithmic`, the exact cap dependence in `AngularSeedLogLoss`, `WidthNormalization.grid_mass`, the actual `AnisotropicSamplingRetention.Output` record, and `AnisotropicDensityPower.output_power`.

## Correct old-support comparison

The hairbrush theorem is applied to the original box's actual measurable `Full` and `Ref` sets. Their carrier, separation, cap, mass, broadness, and physical-ball two-ends conditions are explicit. The top theorem does not accept an already proved hairbrush lower bound or an analytic-energy oracle.

The old-support assumption is literal set containment in the one common width-normalized image of the union of old grid cells. `volume_to_old_cells` uses the proved exact identity

`volume(normalizedSet W (cellUnion δ S)) = δ^(k+2) #S / W^(k+2)`.

Finiteness of the containing grid union justifies the real-volume monotonicity step. Since `W ≥ 1`, replacing the displayed volume by `δ^(k+2) #S` weakens the upper bound. Cancelling the positive factor `δ^(k+1)` leaves `δ #S`. The next step uses `δ ≤ δ/tau`, valid for `0 < tau ≤ 1`, and again weakens the bound before dividing by the positive normalized mesh.

Consequently the returned factor is `(δ/tau)^((m−3)/2)`. There is no extra adverse power of `tau`, no assertion that a new sampled-cell count equals normalized volume, and no overlap premise for pulled-back new cells. Discarding the stronger available normalization factors is legitimate. The ambient dimension is consistently `k+2`; the tube-volume factor is `δ^(k+1)` and the grid-volume factor is `δ^(k+2)`.

## Sparse-density power and logarithms

Writing `s = δ/tau`, the density cutoff is explicitly imposed on `O.density`, the actual selected density, not on the possibly larger original density. For `C ≥ 2`, `eps ≥ 0`, and `O.density ≤ s^(1/3)`, the scalar comparison has exactly the margin

`margin = (m+3)/2 − D + (C−2)/3`.

The theorem requires this margin to be strictly positive. The cutoff is raised to the nonnegative power `C−2`; no reversal of a density inequality is hidden. The scale loss is discarded using `s ≤ 1` in the correct direction. All occurrences of `1/3` here are explicitly real exponents.

`natural_le_seedLog` correctly gives `log(2/δ) ≤ seedLog δ` for `0 < δ ≤ 1`. Positive logarithmic exponents therefore preserve upper budgets for `B,K`, while negative exponents weaken the lower budget for the marked fraction. The opposite comparison used for inverse-log absorption is also correct:

`seedLog δ ≤ [(3/log 2)*a] log(2/s)`

under `a ≥ 1` and `s^a ≤ δ`. The factor includes the additive constants in both logarithms. The proof then applies the uniform inverse-log estimate at `s` and multiplies by the fixed positive factor `[(3/log 2)*a]^(-P)`. Neither logarithm is treated as interchangeable without its required direction and coefficient.

The identity `hairbrushLog k δ = logCoefficient k * seedLog δ` is literal from the definitions, so the reflexive logarithm premise in the actual single-box invocation is valid.

## Density and population retention

`retained_quadratic` derives `O.N ≤ M` from the actual injective original-index map and combines this with `0 < O.density ≤ lam`. Thus

`O.density^2 * O.N ≤ lam^2 * M`.

This is used only to weaken the original-box quadratic hairbrush lower bound to the selected output's quadratic mass. It does not assume that the original density also satisfies the sparse cutoff.

The original-parameter wrapper subsequently uses the proved joint mass-retention interface. Its exact factor is

`cRet = (e₀/4)^(C−1) * e₀/[16*depthCoefficient e₀ xLog]`,

with logarithmic exponent `xLog*C+1`. This follows by multiplying the density retention to power `C−1` by the joint density-times-population retention. It does not multiply the separate population loss twice. The wrapper splits the requested scale loss into `eps/2` for the local bound and `eps/2` for absorbing this additional logarithmic factor. Both constants are chosen before the actual mesh, densities, population, cap constant, or output record.

The cap coefficient is also accounted for: the single-box constant has exact dependence `A^(-1/2)`, and the proved comparison for `A ≥ 1` weakens it to the required `A⁻¹`. The constant used in the final estimate is evaluated at cap coefficient one before configurations are quantified.

## Exact boundary

The conclusions are conditional on the actual original geometric/mass/broadness/two-ends hypotheses, the explicit complementary scale relation, fixed logarithmic budgets, and an `AnisotropicSamplingRetention.Output` linked to the same original `Full` array. The output record carries previously constructed geometric and retention data; neither reviewed theorem fabricates its existence. The forthcoming actual-box adapter must instantiate these conditions from the selected spatial box.

The physical density parameter used by the measurable hairbrush must satisfy `lam ≤ 1`. It must not be confused with the unscaled finite density `V.density`, which can be as large as two; the existing width-normalization adapter provides the physical density. This distinction is preserved in the reviewed statements.

These modules prove the individual sparse-density branch and its return to original box parameters. They do not construct or sum all original angular/spatial boxes or remove the global two-ends condition.

## Additional check: actual good-box wrapper

After the two principal reviews, `AngularBoxLowDensity.lean` was also read in full and independently recompiled with no diagnostics. Reviewed SHA-256: `6bf1444de00f3cb9b6af50e70344dbab3fab3dedb4b0251cdcace7995d1a9588`. No defect was found.

Its `construct` uses the exact `AngularSpatialSampling.Package U`, the same good box `q`, and the same `U.output q` in both the branch test and the lower-bound invocation. Actual box geometry, original-cap and separation inheritance, measured upper density, marked mass, nestedness, broadness, physical-ball two ends, and original-cell support are derived from the package and inspected construction interfaces. The width test proves the physical density is at most one. The literal broadness constant is proved at least one rather than replaced by an unrelated constant or a different reference shading.

The substituted fixed natural-log powers are precisely `(bLog,kLog,qLog,xLog)=(1,2,1,1)`, with all coefficients taken from the reviewed dimension/normalization budgets before the concrete family, refinement, package, box, and mesh are supplied. The conclusion is expressed in the original box's physical density and original box population. The remaining premises are the original family geometry, the explicit logarithm/scale branch conditions, and the actual package, whose separate constructor is available; there is no supplied per-box Input, cap-population estimate, or desired old-cell lower bound.
