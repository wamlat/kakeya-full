# Independent review: volume, density normalization, real-scale localization and rescaling

Reviewed current `TubeVolume.lean`, `DensityNormalization.lean`, `ScaleChoice.lean`, `UniformLocalization.lean`, and `Rescaling.lean` after the global cap-thinning checkpoint. No edits were made. No false statement, hidden volume normalization factor, scale-exponent error or quantifier defect was found in these modules.

## Actual Euclidean tube volume

TubeVolume proves compactness of the exact closed width-delta neighborhood of a unit axis segment, including endpoint caps. Its image-of-compact-product identity is valid even for nonpositive delta; quantitative bounds use delta>0. The standard Euclidean volume is used, and `ball_volume_scale` obtains exactly `r^k * unitBallVolume(k)` from Mathlib's Haar ball theorem with the Euclidean space's actual dimension k.

The upper cover has `ceil(1/delta)+1` axis samples and radius2delta balls, so at 0<delta≤1 its constant `3*2^k*unitBallVolume(k)` multiplies delta^k/delta. The lower cover uses centers spaced2delta and closed balls of radius delta/2. Their center distance strictly exceeds the sum of radii, so the proof does establish disjointness, including closed boundaries. There are `floor(1/(2delta))+1` samples in the actual [0,1] segment. The lower constant is `unitBallVolume(k)/2^(k+1)` and the argument remains valid for delta>1. Real measure is used only with finiteness justified by compactness or finite unions. Both constants are positive and chosen before the actual tube and delta. Writing delta^k/delta instead of delta^(k-1) avoids the natural-number subtraction edge case; for positive dimension it is the expected exponent. A UnitTube in dimension0 cannot exist, so the final universal quantification there is harmlessly vacuous rather than a claimed nonzero tube construction.

## Density clamping

DensityNormalization starts from actual equal positive integer shading counts K with K≤C/delta, C≥1 and 0<delta≤1. It chooses genuine subsets of cardinality min(K,floor(1/delta)). The retained integer count is positive and at least K/(2C); resulting lambda=delta*K0 lies in (0,1] and obeys the stated lower bound. Tube directions and positions are unchanged, every shading is a subset, and union monotonicity is proved. It gives comparable counts with equality at the lower endpoint. The equal-cardinality and upper-count premises are explicit inputs, to be supplied by geometric tube counting and a previous density class selection; neither is silently derived here.

## Scale choice and two ends

ScaleChoice's chosen J gives delta≤2^(-J)<2delta, with J≤log(1/delta)/log2. At delta=1 it allows J=0; no division by a vanishing logarithm occurs because log2>0. The separate class-budget lemma includes the extra top class and is uniform when lower=upper.

UniformLocalization chooses a genuine finite restriction and rho in [delta,1], first at one of those dyadic scales, then extends all-radius control down to the actual delta using monotonicity and max(r,bottom). The factor grows from2^alpha to4^alpha exactly because bottom<2delta≤2r. alpha≥0 and nonnegative mass are explicit and are required for monotonicity of real powers. The mass lower bound is rho^alpha times original mass, with no unstated dependency on scale. The finite weighted version permits zero weights and empty input; no positivity is inferred in those cases. The measurable version explicitly assumes measurability and finite measure of Y, while allowing infinite ambient volume; every real-measure monotonicity comparison retains a finite upper set.

Both localization theorems require the original set to lie in a unit ball about a supplied center. They do not by themselves partition an arbitrary bounded tube family into such balls or assert a uniform result for an unbounded shading. In an application those fixed-radius covering/dilation reductions must be supplied.

## Exact rescaling and application boundaries

Rescaling uses the exact spatial map `(x-origin)/rho`, and integer translation of labels produces exactly mesh delta/rho. The label map is injective, so individual and union cardinalities are truly preserved. Actual unit directions remain unchanged. Tube axis parameters in an interval [a,a+rho] become parameters in [0,1], and distance errors are divided by rho. Comparable density changes from lambda to lambda/rho, and the cap coefficient changes exactly from A to A*rho^(-m). The latter identity is valid for arbitrary real m with rho>0, rho≤1; it does not depend on an integer cap exponent.

Three explicit interfaces matter for assembling a new normalized configuration:

1. `rescaled_admissible` assumes a genuine tube-axis interval of length rho containing the witnesses for all selected shaded cells. A spatial ball restriction alone need not give interval length exactly rho: the direct triangle bound typically gives a fixed multiple of rho plus width*delta. An application must derive an appropriate interval and account for these fixed factors before using the theorem. This is an honest premise, not a defect in the theorem.
2. Direction separation is unchanged by spatial rescaling, so a delta-separated family is not automatically delta/rho-separated. The now-proved CapThinningGeometry global selection supplies a suitable subfamily with coarse projective separation and cap preservation.
3. To obtain a normalized configuration one also needs delta≤rho (supplied by UniformLocalization), an upper density lambda/rho≤1 or density clamping, and the explicitly stated bounded localized axis-base condition. These are not conclusions asserted by the rescaling algebra alone.

No missing dependence on original translation, direction, tube count or scale was found in the proven constants. The remaining items above are assembly obligations at the call sites, not counterexamples to the reviewed declarations.
