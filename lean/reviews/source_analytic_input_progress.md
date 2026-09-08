# Weaker analytic inputs for the source pivot

The individually compiled and exact-source audited modules `LiftedCumulativeInput` and `SourceMarkedPivotInputs` remove the stronger analytic input assumptions from the normalized original marked theorem. They are development additions, not part of published checkpoint 19.

The lifted predicate puts the same arbitrary positive error into its cumulative density and scale powers. Its constant precedes the actual cap coefficient, scale, density, population and family. Every actual comparable family maps to cumulative data with unchanged tubes and cells. On a nonempty integer shading, lambda >= delta/2. Evaluating the source premise at epsilon/2 therefore pays its extra density error by another epsilon/2 of scale error, with exact constant factor 2^(-epsilon/2). The empty family is handled directly. No Jensen inequality or positive density-exponent restriction is needed by this conversion.

The source pivot wrappers assume only `AbsoluteDiscreteEstimate` for the base and `LiftedCumulativeInput` for the lift. They apply the actual whole-tube thinning and paired-error adapters to the already audited positive-p source-minimum theorem. The literal fourth-power, original-union and source-N-notation conclusions are exposed.

Remaining distinction: these wrappers still take `AdmissiblePivotSlabs.Hypotheses`, so their marked families have separation delta and strict density ratio 2. They do not yet prove arbitrary fixed marked normalization. Also, these analytic predicates cover delta <= 1; a separate actual bounded-scale completion is being added to accept source hypotheses stated only at eccentricity >= 2.

Individual audit: LiftedCumulativeInput, 13 all-local declarations / 11 theorem declarations, SHA 01cc887125d6677b4f015026c6e9af766fba7b1244196db7e2a6a272aed548cc; SourceMarkedPivotInputs, 3 public theorem declarations, SHA f25e37dc723c01a6a43de4700dc816604af4d6d163a66ba15b1efc9e15d1fed7. Dependencies are standard Lean foundations only.

## Completed source eccentricity cutoff

`DiscreteScaleCompletion` now proves a positive fixed constant for any lower mesh a>0 and every real density exponent. The actual cap-cover count controls M/A, and nonempty integer shadings force lambda>=delta/2. Consequently scale and density powers are uniformly bounded at delta>=a and the normalized target is at most one actual occupied original cell. Empty families are handled directly. The `complete` theorem joins this with any supplied small-scale estimate.

`SourceAnalyticInputs.Base`, `.Lifted` and `.TwoEnds` assume estimates only at delta<=1/2, precisely eccentricity N>=2. They quantify their fixed geometric/input parameters before original configurations. Whole-row fixed-cap selection preserves this mesh; the lifted input uses the epsilon/2 density-error conversion. The coarse completion supplies the omitted meshes without an analytic hypothesis. Public `.to_discrete`, `.to_two_ends`, `.globalize` and `.globalize_measurable` all compile and pass the unchanged declaration auditor.

`SourceMarkedPivotSmallScaleInputs` now gives all three source-minimum pivot conclusions from these small-scale-only base/lifted inputs. Arbitrary fixed marked-family normalization remains a separate active proof. The older all-scale input adapters are kept as useful intermediate theorems, not substituted for the literal weakest source premise.

Final additional audit hashes:
- DiscreteScaleCompletion: 2c9752ba6d09715aa2025da4e030ecf0f68087122c7ee4c70f66a30bb6aa5aba (5 all-local, 4 theorem declarations)
- SourceAnalyticInputs: 0e41e594931a2ca53beebfc0297e6ca99b0d1d09c5eedb0ccb1e980a4c40b322 (10 all-local, 7 theorem declarations)
- SourceMarkedPivotSmallScaleInputs: c776d76661bd93493c9c4a2aec1e9fff799cff780dcb3ab6c4dc5a9f12942a5f (3 all-local/theorem declarations)

All five new source-input modules compile without diagnostics and use only propext, Classical.choice and Quot.sound. The final independent source review and integrated checkpoint verification remain distinct checks.
