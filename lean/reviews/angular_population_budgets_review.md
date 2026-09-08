# Angular population and logarithmic budgets: separate review

Reviewed the frozen sources `SpatialGridPopulation.lean` and `AnisotropicSamplingBudgets.lean` against `AngularRestrictedMeasurable`, `SpatialMarkedGroups`, `AnisotropicSamplingInput`, and `AnisotropicSamplingRetention`. This was a read-only statement/proof review; no frozen source was edited and no additional premise was inserted. No substantive mathematical defect was found in either reviewed module. Their source hashes at review are listed below.

## Actual old support and summation

`SpatialGridPopulation.box_full_union` is a literal set equality, including half-open grid-cell boundaries. The spatial family reindexes the existing tube and shade functions, while the measurable full sets use one common `normalizedSet W`. Thus `refined_full_union` identifies a refined box union with precisely `normalizedSet W (cellUnion δ (refinedCells V width q))`. These are old original-mesh labels, not new grid cells around the transformed shading. Their bookkeeping need not itself be admissible for the normalized tube family: the physical carrier inclusion used by `all_box_counts` is separately proved and supplied.

`all_box_counts` integrates actual physical overlap and cancels the common strictly positive factor `δ^(k+1)/W^(k+1)`. `refined_box_counts` uses width 1 and angular aperture 3, and only then uses the literal inclusion of the selected Ref cells in the old angular group cells. `sum_refined_box_counts` consequently proves

`Σ_g Σ_q #oldCells(g,q) ≤ Csp * 2 * τ^(-β) * #originalUnion`,

where `Csp = overlapConstant k 1 3`. The factor `τ^(-β)` appears once, from the independently proved original angular-piece overlap. There is no extra `τ^(-k)`, no assumed overlap of new sampled cubes, and no loss equal to the number of boxes. The good-box corollary is valid for every supplied mass/eta filter because it only needs that this filter is a subcollection of actual labels. Positivity and retained mass of those good boxes are supplied separately by `SpatialMarkedGroups.construct`.

This matches `AnisotropicSamplingRetention.Output.contained`: each final full shading remains inside the normalized image of its SAME spatial-box original full set. Combining that containment with `refined_full_union` gives containment in the composed map `pieceMap` of the identical `refinedCells`; `TransformedGridSupport.positive_support_card` can then bound each actual sampling support by `(2(k+1)+3)^(k+1)` times that old-cell count. This inference uses its proved Lipschitz map and actual support theorem, rather than treating volume as a count.

## Literal constants and logarithms

`AnisotropicSamplingBudgets` uses exactly the frozen formulas for retention, marked fraction, two-ends coefficient, and broadness coefficient. With `e ≥ e₀ L^(-q)`, `q ≥ 0`, and actual selection depth `D+1 ≤ log(4/e)/log 2+2`, it constructs the fixed coefficient

`Cdepth = (|log(4/e₀)|+q)/log 2+2`

and proves `D+1 ≤ Cdepth L` for `L ≥ 1`. The absolute value safely handles a lower coefficient `e₀ > 4`; all divisions and logarithm monotonicity have positive arguments. The inverse-retention, depth, and real-power exponents are consistent:

- marked fraction lower exponent `-(q+1)`;
- two-ends upper exponent `bLog+q`;
- broadness upper exponent `kLog+q+1`;
- new-density lower exponent `-q`;
- new-population and density-times-population lower exponent `-(q+1)`.

The last bound correctly uses the stronger actual `Output.density_population_lower`; it does not multiply two separate retention losses. `uniform_constants` places all four positive constants before the actual `L,e,B,K,D`. Its dependence on fixed dimension, aperture, beta, and initial budget parameters is allowed and explicit. It introduces no assumption about the selected measurable sets.

There are two genuine application conditions, both honestly visible in the statements/report:

1. `L ≥ 1` is not automatic from `δ′ ≤ 1` when `L=log(2/δ′)`: at `δ′=1`, the log is `log 2 < 1`. A fixed small-scale condition, for example `δ′ ≤ 2/exp(1)`, supplies it.
2. An original-scale budget in `log(2/δ)` cannot simply be relabeled as a budget in `log(2/(δ/τ))`. The latter log can be much smaller. In the complement of the coarse case, the actual condition `(δ/τ)^a ≤ δ` with fixed `a ≥ 1` gives the needed comparison by `LowCellAbsorption.log_scale_transport` and `inverse_log_scale_transport`, with fixed powers of `a` in the coefficients. The reviewed budget module does not prove or assume this geometric scale relation implicitly.

## Exact next composition theorem

For original ambient dimension `n=k+1`, let `F` be the original bounded, separated, cap-controlled, admissible family, let `P` be its actual angular pieces, and let `V_g` be each constructed refinement on an actually kept angular group. Put

- `W = widthFactor (k+1) originalWidth`;
- `d_g = V_g.density / W^(k+1)`;
- `a_g = V_g.depth+1`;
- `eta_g = 1/(4*a_g)`;
- `Y_g = AngularRestrictedMeasurable.Full V_g originalWidth`;
- `G_g = AngularRestrictedMeasurable.Marks V_g originalWidth`.

The next theorem should construct ALL actual good spatial boxes using `SpatialMarkedGroups.construct` with mass parameter `d_g*δ^k`, fraction `eta_g`, physical width 1, aperture 3, and the unchanged actual sets `Y_g,G_g`. The marked fraction and per-tube full lower density prove its marked-mass hypothesis. It should then return an actual `Retention.Output` for every good box, with original density `d_g`, fraction passed to the joint selection `eta_g/4`, and exactly the full/marked box sets returned by the spatial partition. No independent segment or color choice is needed in this wrapper.

The inherited constants are

`B_g = (B*(4/P.eta))*(1+(k+1)/2)^alpha * W^alpha`,

`K_g = (broadCoefficient k beta*(8/P.eta))*(2*a_g)`,

with box marked broadness coefficient `4*Csp*K_g`. The final retention is `e_g = retention k 3 (eta_g/4)` and the output uses its actual new depth `D_gq`; the original depth `V_g.depth` and this new depth must remain distinct.

If original bases are bounded by a nonnegative fixed `R`, their common width-normalized bases remain bounded by `R`. Actual base quantization then proves each box has parallel-box radii `R+2` and `k+4`. Therefore the final base bound is the fixed quantity `baseBound 3 (R+2) (k+4)`, independent of the box label, scale, population, or selected density class. A whole angular group is never treated as one spatial box.

One scalar normalization must be supplied explicitly: the refinement only gives `V_g.density ≤ 2*lambdaOriginal`, so `lambdaOriginal ≤ 1` plus `W ≥ 1` alone does NOT imply `d_g ≤ 1` in every dimension and width. The sufficient fixed test is `2 ≤ W^(k+1)`; it yields `0 < d_g ≤ 1`. It is automatic when original width is at least 1 and ambient dimension is at least 2, and also when the ambient dimension is at least 3 and original width is nonnegative. For smaller dimensions/widths a stronger common width normalization or this explicit test is necessary. This is an assembly condition, not a defect in either reviewed theorem. The parent has assigned the concrete wrapper to `AngularSpatialSampling.lean` with that test visible.

The resulting family of outputs should retain each exact `refinedCells` support identity, the actual good-box population sum, and the already proved global old-cell sum. The parent can then apply the local sampling/pivot theorem to each output and sum using the budget module, with the coarse/log-domain cases kept separate.

## Frozen bytes reviewed

- SpatialGridPopulation: `57b16d013dfb0eb95326ca346beccac56811d54c9c0d1553f5370b4c32fb9731`.
- AnisotropicSamplingBudgets: `dc259f8a0d276e703d4a1408253286e0d009972391deb76c2e776cfec0f48bae`.
- AnisotropicSamplingRetention: `7b81218726795dd4d7fc436be0cd39b227bfba543a49cf7f88c1fad69a2758be`.

## Actual assembly follow-up

The subsequently added `AngularSpatialSampling.lean` was also read independently. Its `construct` and `BoxOutput` implement the preceding composition with the same constants: physical density `V.density/W^(k+1)`, spatial marked ratio `1/[4(V.depth+1)]`, joint effective ratio `retention k 3 (markedRatio/4)`, broadness `Kref*(4*Csp)`, and fixed base bound `baseBound 3 (R+2) (k+4)`. `refined_geometry` uses one composed injective original index for both unchanged directions and normalized bases. `spatial_data` obtains its mass and common-box fields from the actual spatial construction; it does not assume them. `box_output` retains the exact original full sets and inherited all-radii two ends. `old_cell_support` uses the same composed map for every tube in a box, and `total_old_count` retains only the proved angular/spatial overlap. The explicit width-power test supplies `physicalDensity_le_one`; no unconditional low-dimensional shortcut was introduced. No substantive defect was found in this follow-up review.

## Coarse-branch follow-up

`LocalAngularCoarse.lean` was read independently as an adjacent application check. No substantive defect was found. For local angular population, `a=max(1,angular)` guarantees both a cap radius at least delta and a positive fixed coefficient. When `a*tau>1`, the actual radius-one finite cap cover controls the total population; the inequality `1/delta ≤ a*tau/delta`, raised with the explicit nonnegative real m, gives the claimed normalized cap population. The coarse exponent uses the ambient dimension `k+1`, so its cutoff is `delta^(1/[2(k+1)])` and `D≤k+1` follows from the stated real-m range. Zero populations and arbitrary fixed positive density upper bounds are handled. The coefficient `lambdaMax^(1-C)` has the correct sign and normalizes `lambda^C` to at most lambda for C≥1.

At the actual spatial-box junction, the finite old-label family is Comparable at `V.density`, while its physical measurable density is `V.density/W^(k+1)`. The coarse theorem should first be applied at the former density, then weakened monotonically to the latter using W≥1 and C≥1. It must not be invoked as if the finite family had a different exact comparable-density parameter. This is straightforward scalar composition and is not an extra geometric premise.

## Actual high-box follow-up

The frozen-shape `AngularBoxHighDensity.construct` was also read. It applies the high-density estimate to the SAME `U.output q`. Its cap coefficient is exactly `capFactor*A`, and the fixed factor is extracted as `cS/capFactor` in the conclusion, leaving the desired original A inverse. The bound `delta≤delta/tau≤2/exp(1)` proves the required original natural logarithm is at least one. The literal output conditioning uses powers `(x,b,k)=(1,1,2)`. Old support is derived from `box_full_support`; no new sampled-cube overlap is assumed. The existing Package fields already supply measurable geometry, separation, and cap hypotheses. The remaining high-density, coarse-complement, and fixed normalized-scale tests are explicit. No substantive defect was found.
