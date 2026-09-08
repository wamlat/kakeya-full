# Actual localized seed normalization bridge

`LocalizedDirectionThinning.lean` (5 theorems) and `LocalizedSeedNormalization.lean` (6 theorems) are clean-built and full-source audited, with only `propext`, `Classical.choice`, and `Quot.sound`.

The thinning theorem selects actual complete original shadings at an arbitrary target direction mesh. It uses the proved full cap hierarchy at max(original mesh,target), derives all smaller-radius cap tests from the old endpoint, and applies an actual fixed-palette separation coloring. At a common localization radius rho and dilation L>=rho, the retained count is at least M rho^m/[C(k,m) A]. The new cap coefficient depends only on dimension and m; standard target separation is proved.

The normalization theorem assumes an actual localized finite family: every original shading lies in its own radius-rho ball, all densities are comparable to s/delta, and full center-ball two-ends tests hold at delta<=r<=rho. It constructs a genuine unit family at scale delta/[K rho], density s/[K rho], and width max(1,width). The single coefficient K is max(8 max(1,width),the explicit local tube population constant). Its second term proves the new density is at most one from geometry. Complete selected shading cardinalities survive exactly, and the new union cardinality is at most the original localized union cardinality. Two ends holds at all new radii with coefficient B K^alpha. There is no bounded-base premise, no density clamp assumption, and no spatial cluster loss: every tube uses the same spatial homothety about the original zero-grid origin.

Next source `FiniteGridLocalization.lean` (5 theorems) has clean compilation and is being built/audited. It constructs the actual common radius and common density classes directly on physical Euclidean grid-cell centers. Its Selection record provides rho^alpha lambda<=s, actual comparable sizes s/delta to2s/delta, original-cell subsets, full two ends, and count M/[(J+1)(D+1)]. Both actual class depths are logarithmic in delta independently of lambda.

Remaining: standard indexed family from this selection, initial fixed dilation ensuring the one-radius covering premise, application of the uniform two-ends seed to the normalized selected family, and exact radius/density/error absorption into the target real-cap seed.

## Further completed interfaces

`FiniteGridLocalization.lean`5 and `FiniteLocalizedFamily.lean`11 are now clean-built and full-source audited on standard foundations. The latter constructs the standard-indexed actual localized family, inherits original cap bounds, retains actual original subsets, proves count>=M/[(alpha+3)L(delta)^2], and derives the geometric radius-density bound lambda<=C(k,width)rho^(1-alpha).

`SeedCoverNormalization.lean`10 is clean-built/audited. An initial common dilation by1+max(1,width) makes all original full shadings fit unit balls around their own tube bases. It preserves union cardinality exactly and leaves the original cap coefficient unchanged (the smaller testing scale is handled rigorously). Thus the common-localization covering premise is constructed from actual original tube admissibility.

`LocalizedSeedApplication.lean`3 is clean-built/audited. It directly applies the proved uniform two-ends seed to the actual normalized/thinned family, giving a fixed positive constant before the original localized family and all scales/densities/cap constants: c A^-1 delta^((m-3)/2+epsilon) s^2 rho^((m-1)/2) M<=original localized unioncard. No analytic seed premise is supplied.

Remaining at this point is globalization algebra and final uniform-exponent assembly. `SeedGlobalizationAlgebra.lean` and `CoveredSeed.lean` are in development for this step; they are not part of this completed checkpoint until compiled/audited.
