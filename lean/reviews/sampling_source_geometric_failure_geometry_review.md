# Separate review of the actual source geometric probability wrapper

Read `SamplingSourceGeometricFailure.lean` at SHA `e3ce1d27d2e010fcdf44aedb56576b0ab9bee0e481a1088570f1a08c86ae4627`. This agrees with the supplied frozen hash. No mathematical, same-data or quantifier-order defect was found. No source edits or recompilation were performed for this read-only review.

The final probability is literally measured by `SphereNetSourceFailure.rawLaw h`. The equality with the generic density/ball law is definitional. Original support, full/marked cell-intersection probabilities, axes and physical mesh are unchanged. The chosen ball depth and all bottom/depth estimates refer to this same original support.

The fixed dimension, width, base bound, upper axis length, positive separation constant, positive lower density constant, `s` and `alpha` occur before the mesh cutoff. All families and later density, upper density constant, marks and conditioning coefficients occur afterwards. The cutoff also enforces `separation*delta <= 1`, so applying actual direction packing is valid even for arbitrary fixed positive separation normalization.

The tube population bound is derived from actual separated directions. The ball-test count is derived from the bounded original support and the constructed logarithmic depth. Their product has the true `N^(2*ambient-1)*log(N)` form; the generic source-count helper weakens this to a fixed multiple of `N^(2*ambient)` before the stretched-exponential threshold. It neither drops the spatial/separation prefactors nor assumes the resulting test count. Zero placeholder inputs are supplied only to the unused second component of that counting helper; they do not replace a needed actual geometric count.

The source lower density `lambda >= delta^s` gives a full mean at least `c0*N^(1-s)`. The real ball cutoff is at least `ballCoefficient*c0*N^(1-s-alpha)` because `B>=1`, each actual test radius is at least `delta`, and `alpha>=0`. The two positive exponents are justified by `0<s<1` and `alpha<1-s`. The upper restriction `alpha<=1`, used by the physical mean theorem's fixed coefficient, follows from the same strict gap. Actual cell/ball means are obtained from the original measurable full shadings, rather than a caller-supplied expected-count bound.

The result is the separate probability `<1/8` for the broad source density band and full-ball cutoffs. It does not claim a narrow `[2*mean/3,4*mean/3]` band, angular probability or joint success; these are separate interfaces. The actual mean-based ball cutoff is a valid stronger finite testing interface for the source all-ball estimate, and its required positive-power lower bound is proved. No `SampleGood` or favorable outcome is assumed.

This source is outside the already published 381-module checkpoint 21. No frozen source, registry, verifier or output package was modified.
