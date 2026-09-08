# Actual sphere-cap upper measure

`SphereCapMeasure.lean` is frozen and clean-built. It uses the shared `KakeyaOperator.Direction` sphere subtype and `sphereMeasure = volume.toSphere`; no sphere measure bound or analytic estimate is assumed.

For an oriented chord cap around a unit direction v, its actual radial cone consists of `t*w` with `0<t<1`. The inequality `dist(t*w,t*v)≤r` puts this cone inside the literal radius-r unit tube with base zero and direction v. Mathlib's proved polar-coordinate identity `Measure.toSphere_apply'` then expresses cap measure as ambient dimension times cone volume. Applying the already proved tube-volume upper bound gives

`sphereMeasure.real(chordCap v r) ≤ n*U_n*r^(n−1)`,

where `U_n=3*2^n*TubeVolume.unitBallVolume(n)` and `0<r≤1`.

A projective cap is contained in the union of the chord caps centered at v and −v. Both caps are proved measurable, as is the actual projective-distance function. Consequently

`sphereMeasure.real(projectiveCap v r) ≤ C_n*r^(n−1)`,

with explicit `capConstant n = C_n = 2*n*U_n`. This is positive for `n>0`. The real exponent is literally `(n:Real)−1`, so there is no natural-subtraction ambiguity.

The main downstream APIs are:

- `finite_cover_upper indices center S hr hr1 hcover`, for a finite set of centers;
- `indexed_cover_upper center S hr hr1 hcover`, for `center : Fin M → Direction n`;
- `indexed_cover_upper_ennreal`, with the same arguments and an extended-real measure conclusion.

The cover premise is the actual pointwise relation: every v in S lies within projective distance r of some listed center. The conclusion is at most `C_n*r^(n−1)*M`. The covered set S is arbitrary and need not yet be measurable; sphere measure is proved finite on every set, so both its real outer measure and the ENNReal formulation are valid. Finite subadditivity supplies the conclusion; neither desired cover cardinalities nor level-set measure bounds are assumed. Actual finite level-set covers/witnessing tubes are being constructed in the separate `IndicatorWitnessCover` work.

The result is the geometric spherical-measure input to manuscript (9.7). It does not assert measurability of the Kakeya maximal supremum or any interpolation theorem.

Verification: clean compilation with zero diagnostics; production exact full-source environment audit of 26 local declarations, including 21 theorem declarations. There are 15 named source theorems and five definitions. All axiom dependencies are among `propext`, `Classical.choice`, and `Quot.sound`; no custom axiom or admitted proof was introduced. Evidence: `SphereCapMeasure_audit.json`, `SphereCapMeasureSourceAudit.lean`, and `SphereCapMeasure_axioms.log`.

Frozen SHA-256: `039f2aa10b949ddd6bf7ab6c472af047c34454c9aea15834aa2536d6b522e245`. No frozen checkpoint source or shared registry was edited.
