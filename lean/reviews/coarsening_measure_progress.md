# Actual coarsening, spatial pruning geometry and measurable grid realization

6 September 2026. These results are continuing components of the manuscript audit; they do not assert the full seed or pivot theorem.

## Coarsening and coarse base-estimate application

`Coarsening.lean` constructs the coarse label by placing each fine cell center in its actual half-open coarse grid cell. The coarse center is within half the dimension times the coarse scale. Image shadings are admissible at the enlarged fixed width. Actual tube-ball counting bounds every coarse fiber by a fixed constant times r/δ. Consequently coarse shading cardinality is bounded below by δ/(Cr) times fine shading cardinality. Disjoint heavy fibers pay their actual fine-cell mass; no abstract packing assumption substitutes for this fact.

`CoarseFamily.lean` invokes the complete cap-preserving thinning theorem on the actual coarse family, constructs an injectively reindexed normalized family with coarse direction separation, and applies the cumulative form of the base estimate. Its main theorem chooses c>0 before all families, scales, cap coefficients and densities and proves

c A⁻¹ δ^m r^(−d+ε) s^p M ≤ number of actual coarse union cells,

for 0<δ≤r≤1 and fine shading counts at least s/δ. The only analytic premise is the original concrete DiscreteEstimate; the coarse estimate is derived, not assumed. It requires m≥0, p≥1 and fixed original width/bounded-region parameters.

## Actual spatial ball bounds

`BallPruning.lean` defines survivors by deleting every fine cell lying in an original heavy coarse fiber at any of the actual dyadic scales. Actual coarse-grid ball covers and fiber summation bound every ball of radius at least δ. The all-radius variant uses the original bounded region to handle radii above one. Its constants are dimension/bounded-region constants times the common fiber threshold. These geometric statements alone do not promise retained mass. The independently authored `HeavyIncidence.lean` and `PrunedIncidence.lean` now supply actual retained incidence from the base estimate; their precise cumulative, rather than per-tube-comparable, output is recorded separately.

## Exact measurable realization

`GridShadingMeasure.lean` realizes finite shadings as unions of actual centered half-open grid cells. Membership is equivalent to the unique grid label lying in the finite shading, at every point including boundaries. Measure equals δ^k times the finite cardinality. Total incidence, union measure, pointwise multiplicity, angular broadness and group overlap transfer exactly.

An actual cell meeting a radius-r ball has its center in the ball enlarged by kδ/2. This proves measurable two-ends from actual finite center-count tests, with factor (1+k/2)^α. Tests above unit radius use the finite total mass and B≥1. No null-boundary convention or unproved continuum ball assumption is used.

`WidthNormalization.lean` applies one common positive homothety, with W=max(1,width+k/2), to every realized shading. The shortened original axes are extended to actual unit segments. Physical radius is now δ; directions remain unchanged. The inverse map transports every actual incidence pattern. Individual and whole-union volumes carry the same exact factor W^(−k). All two-ends ball tests transport with the explicit W^α factor and the correctly transformed lower testing radius. Independent tube translations are never used to control a union.

## Remaining scope

These modules close concrete interfaces. The general analytic seed still requires assembly of localization, angular grouping, density recovery, rescaling and all group losses. The pivot still requires its geometric incidence/collision and lifted application assembly. The maximal-operator passage is separate. Compilation checks the exact statements and explicit assumptions, not these remaining conclusions.
