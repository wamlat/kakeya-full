# Checkpoint 15: sampling and six-dimensional core statement review

Read-only review of the current frozen sources. No edits or duplicate source/verifier audit. Reviewed the first three modules independently of their author. `SixDimensionalCore` was originally authored by this reviewer, so its fresh linkage recheck is not an independent authorship audit; its external statement review and kernel audit are separate checks.

## Verdict

No substantive mathematical statement-linkage defect or overclaim found in these four files. The local sampling application now constructs the probability data and outcome, combines both sampling alternatives, and returns a genuine bound on the specified OLD finite cell set. The four theorems do not claim the unrestricted implication M6(4) -> M6(33/8), and they do not discharge its remaining globalization hypotheses.

## SamplingMeasurablePivot

`low_or_pivot` starts with actual `SamplingNormalizedMeans.Input`, actual separation/cap geometry, a high-density cutoff, and fixed logarithmic conditioning. It does not ask the caller for probability arrays, a high-cell set, a narrow band, a favorable random realization, or an assumed sampled estimate. All of these come from `SamplingMeasurableAssembly`.

The same normalized full/marked arrays and same coupled outcome are passed to the marked pivot. The equalizer is min(c0,1), the row ratio is C0/equalizer, and the expected full density is exactly equalizer*lambda/delta. This preserves the previously verified exact factor-two sampled density. The theta inverse budget is correctly derived from the actual lower bound with fixed coefficient choice(ratio*K0,beta)^(-1) and exponent kLog/beta. It is not replaced by the raw K budget. The low branch is weakened from the count of actual low cells to the count of the same available support E; this is valid and sufficient downstream.

Both the scale cutoff and positive estimate constant precede every actual family, density, marked fraction, cap coefficient, B and K. The fixed outer c0,C0 and logarithmic coefficients are not allowed to vary silently with the scale.

## SamplingHighDensity

The low-cell normalization is exactly cLow*xi*lambda*M/[delta*log(2/delta)], with cLow=1/[2*ratio*highCoefficient]. `LowCellAbsorption.uniform_low_cap_bound` genuinely absorbs the inverse marked/log loss using positive margin m+1-D and C>=1. Consequently D<m+1 is sufficient HERE. This is not a proof that the complete angular globalization works under only D<m+1; that later argument has its own stricter conditions and other cases.

`construct` takes the minimum of two fixed positive constants to combine the actual low and high alternatives. No low outcome, support bound, or desired estimate is supplied as an extra premise. `all_exponents` weakens alpha to min(alpha,1/4) before choosing constants; since delta<=r<=1, the original r^alpha two-ends inequality implies the weaker-exponent inequality on the SAME sets. The weakening does not create marked broadness or remove the two-ends condition.

The result still explicitly requires lambda>=delta^(1/3) and delta<=delta0. The deterministic low-MARKED-CELL branch is therefore closed inside the high-density regime. It must not be confused with the distinct low-DENSITY angular branch lambda<delta^(1/3), which this module does not handle.

## SamplingOriginalCells

The conclusion concerns an actual finite ORIGINAL cell set S. Each actual Full_i must be contained in the literal common map `pieceMap u tau W q` of cellUnion(delta,S). `TransformedGridSupport.positive_support_card` constructs the target-cell cover and proves its count is at most (2n+3)^n*#S, for n=k+2. It covers all positive-intersection target cells, not merely projected centers. Dividing the estimate constant by this fixed dimension factor is correct. There is no additional tau or W factor: tau<=1 and W>=1 give the proved Lipschitz bound into the delta/tau grid.

All geometry, sampling hypotheses and logarithmic budgets refer to the SAME transformed scale delta'=delta/tau. The resulting constant precedes u,q,S,W,tau and the actual family. Normalized volume is never substituted for old-cell count, and overlap of sampled cubes or their pullbacks is never assumed. The input `Input` is still an actual-geometry hypothesis in this module; the joint normalization and spatial constructions must be composed with it to start from a raw angular piece.

## SixDimensionalCore

The base is exactly `DiscreteEstimate 6 5 4 4`, and the actual lift is `DiscreteEstimate 7 4 (7/2) (7/2)`. Both are proved from `FractionalSeed`; no published-result axiom or projection premise remains. The specialization uses original ambient six and lifted ambient seven, not eight.

The exact marked bound is c*A^(-1)*delta^(7/8+eps)*lambda^(15/4)*M<=#E, with D=33/8, C=15/4 and 5-D=7/8. The literal full-union variant simply uses E=F.unionCells. Its constant is uniform before the actual configuration, but the marked broadness, full two ends, fixed width/base normalization, cap-five condition, comparable full density, and logarithmic conditioning are all retained through the visible hypothesis record. The density exponent is not relabeled as 33/8 under arbitrary-shading hypotheses.

## Remaining M6(4) -> M6(33/8) boundary

The analytic seeds are already available. To obtain the unrestricted measurable M6 conclusion, one must still finish the uniform all-case angular composition, including coarse normalized scales and the low-density branch, and sum actual original piece counts. The newer joint full/marked, spatial partition and old-grid overlap modules address substantial geometric interfaces but these four frozen files do not themselves perform that complete composition. Conditioning expressed at the original scale must be transported to log(2/delta') using an actual scale relation; it cannot simply be renamed. Fixed c0,C0 are available from the new density construction, while the dimensionless lambda<=1 normalization must still be justified at the intended interface.

One then needs the unrestricted two-ends removal with correct density accounting to obtain exponent max(33/8,15/4)=33/8. The discrete-to-measurable occupancy adapter is proved conditional on the unrestricted discrete estimate, but does not supply that missing estimate. Finally the manuscript's arbitrary-position/geometric-convention formulation requires its uniform normalization/globalization link; the current statements have fixed outer base-radius and width parameters. The claimed maximal-operator consequences also have separate interpolation/convention scope.

There is no basis in these four sources for marking the unrestricted implication, the recursive unrestricted real-cap pivot, or all paper conclusions complete.

## Reviewed source fingerprints

- `SamplingMeasurablePivot.lean`: `a7897e130bd6950409f5715038e4a898e775237dc7e7d8661aa989d76f88030b`.
- `SamplingHighDensity.lean`: `38f190d7ddacfef7783bdb417d88b0a3b438f2858f80ad63129c518f84e482ef`.
- `SamplingOriginalCells.lean`: `b7fb8229519e4e3a6c2c17fc34c7fee11c59fb6deb49b567890e66eb5b0f8bd4`.
- `SixDimensionalCore.lean`: `b37e9ee19d97d10e487534d25df89c00d5f71432b0fb5e1b4599d7cdc19c4db7`.
