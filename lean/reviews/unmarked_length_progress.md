# Named original-axis-length adapters for Propositions 7.1 and 8.1

Both new modules are frozen, clean-built with matching oleans and zero diagnostics, and exact-source audited PASS: 7 named source theorems, 15 local theorem declarations and 17 local declarations total, all standard-only. No forbidden constructs were found. They are outside the already frozen checkpoint20 and do not modify any existing source, verifier or registry.

`UnmarkedLengthEstimates.from_two_ends` consumes any proved `TwoEndsDiscreteEstimate n m D C` with m>=0,C>=0 and returns an estimate for actual original axes with any fixed length ceiling. Original cell centers must actually lie in their own `SamplingGeometry.lengthCarrier`; original full rows have arbitrary fixed positive lower/upper density multiples and actual full two ends. The fixed width, separation, base-radius, length ceiling, row multiples, B, alpha and requested error all precede the resulting constant; actual delta,lambda,A,M,axes,individual lengths and full rows follow it. No normalized family or marked/angular selection is supplied by the caller.

The same-label family uses the proved common dilation W=max(1,lengthUpper). It has delta_new=delta/W, lambda_new=lambda/W, unchanged directions/rows/union, fixed width and separation, base-radius R/W, and unchanged cap coefficient A. Because the public original exponent is any fixed alpha>0, the module first proves the actual ball inequality at alpha0=min(alpha,1); this follows directly from r<=1 and the original full two ends. The normalized coefficient is B*W, fixed before configurations. The proved wide-row estimate then normalizes original row cardinalities internally. No factor depending on delta enters its two-ends coefficient.

`from_discrete` instead consumes any proved unrestricted `DiscreteEstimate n m D C` with m>=0,C>0. It uses `OriginalLowerDensity.from_discrete`, so the actual original family needs only a fixed positive lower density multiple. There is no upper-density hypothesis, no lambda<=1 restriction and no full-two-ends condition. Empty families are included. The actual original union is on the right, with no new grid-cell inflation or measure comparison.

The scalar normalization factor in both theorems is explicitly

    (W^-1)^(m-D+eps) * (W^-1)^C.

The exponent m-D+eps may have either sign; the proof uses the exact real-power identity at positive bases. The factor is positive and fixed before configurations. The actual cap exponent remains m and the original population remains M.

`SourceUnmarkedLengths.angular` composes this actual adapter with the full positive-p angular theorem using only `SourceAnalyticInputs.Base` and `.Lifted`, both required only at N>=2. It preserves the exact source D=(2m+3+dprime)/4, C=(p+2q+4)/4, D<m and sparse-margin conditions, and every p>0 with q>=2. It concludes on the actual original bounded-length family and original occupied-cell union with arbitrary fixed density multiples and geometry.

`SourceUnmarkedLengths.globalize` consumes only `SourceAnalyticInputs.TwoEnds`, the source absolute-cap N>=2 premise. It returns the actual original bounded-length unrestricted conclusion at set exponent D and density exponent max(D,C). D>=1 ensures the output density power is positive, so all source C>0 are covered. There is no original two-ends or angular hypothesis, no upper row bound and no original lambda<=1 restriction.

The two source hashes are:

- `UnmarkedLengthEstimates.lean`: `9a2ceb7a87aa23d7b86491124c777ef6756baa6b9ab5d6a1e91c99e1275984fe`
- `SourceUnmarkedLengths.lean`: `1fad383899933828f56fb22a0e9e4576fdf6adabdb50aa05159de83459c03217`

Remaining named-interface distinction: `MaximalShading.Estimate`, `MeasurableEstimate` and `VolumeMeasurableEstimate` still literally refer to unit original axes and their actual unit-tube volumes. Their unit-axis main conclusions are already proved. A separately named assertion of the same actual-volume formula for individually varying comparable lengths must also compare each old tube's volume with its containing normalized unit tube. A fixed positive lower length bound supplies a uniform mass ratio; the existing upper-length carrier inclusion alone does not. These two finite-cardinality adapters do not assert that unproved volume ratio. This is a fixed-geometric-convention extension, not a failure of the unit-axis theorem (1.1).

Validation uses Lean4.33.1 and pinned mathlib `0df444a360eaa60ab8c11dca51a86af692955474`. The production all-declaration AUDIT is appended to each entire exact source and compiled; no custom axiom or supplied output theorem is introduced. The machine-readable result is `unmarked_length_audit.json`. The parent owns integrated verification/publication; independent review has been requested.
