# Read-only review of grouped normalization and its two-ends application

Reviewed the frozen `LocalizedGroupedNormalization.lean` at SHA-256 `86c4426e10b71fc3cb249e4c2e05ec7f42fbdafd19397dd2342ce0b91476e2dd` and the final clean `LocalizedTwoEndsApplication.lean` at SHA-256 `f94be66373842f91d597b4459789be71fcd1df6cf01053043ce78adbd656f21e`. Also checked the normalization report and supporting thinning, tube-ball density, lattice-rescaling, and two-ends predicates. No mathematical defect was found. This is a separate statement/proof cross-review, not a replacement for the owners' exact-source Lean/axiom audits.

**Genuine normalized configurations.** The output is a literal `ShadedConfiguration`, with width `W=max(1,width)`, unit target separation, base radius `(6W+1+n)/K`, mesh `delta/(K*rho)`, and density `nu/(K*rho)`. Here `K=dilationConstant(n,width)` is fixed before any family or scale. Its normalized density upper bound is derived from the actual local tube-ball grid count and comparability; it is neither assumed nor obtained by changing density metadata. The actual short axis interval is extended to length `K*rho` from the same bounded starting point, which justifies its true rescaled unit tube and base bound.

**Cap thinning and correspondence.** The construction uses proved finite cap thinning at `max(delta,delta/(K*rho))` and fixed coloring. It covers both possible orders of these two scales, including `K*rho>1`. The small-scale cap transfer uses the endpoint cap count, so the new cap coefficient `Q=capConstant(k,m)` is independent of the original `A`. All selected rows are the complete corresponding localized rows under an injective common integer-label shift. The population lower bound is `M*rho^m/(T*A)`, with fixed `T=retentionConstant(k,m)`. Thus there is exactly one original inverse-cap loss. The hypotheses `m≥0`, `0<delta≤rho≤1`, and `A≥1` used in these monotonicity and thinning steps are explicit.

**Two ends and old unions.** Per-bin selection costs the proved factor `2*binCount(n)` in relative two ends; rescaling changes the coefficient to `2*binCount(n)*B*K^alpha`. This coefficient is fixed before all configuration data and is proved at least one. At normalized radii whose preimage exceeds `rho`, the total row count supplies the bound, so the output indeed satisfies the complete `FullTwoEnds` predicate. Different bins may use different snapped origins. Summation first bounds each shifted union cardinality by its original bin union cardinality, then uses the disjoint old-cell bin sum. No disjointness or common physical map across separately normalized bins is inferred.

**Application and generalized powers.** `localized_bound` chooses the normalized geometry, normalized two-ends coefficient, and positive estimate constant before `M,F,delta,rho,s,A` or the localization centers. It then constructs the partition and every normalized configuration itself. It assumes an explicit `TwoEndsDiscreteEstimate` and the actual original localization/relative-two-ends hypotheses; it does not assume a chosen partition, selected count, output density, cap-normalized family, or desired local estimate.

Writing `x=m−D+eta`, the exact rescaling/population product is

`[c Q⁻¹/(T K^(C+x))] A⁻¹ delta^x nu^C rho^(m−C−x) M`.

Since `nu≥s/binCount(n)` and `C≥0`, replacing `nu` costs exactly `binCount(n)^C`. The remaining exponent is `m−C−x=D−C−eta`; because `0<rho≤1` and `eta>0`, the stronger factor can be weakened to `rho^(D−C)` in the displayed conclusion. All real-power bases are positive; no unwritten sign condition on `D` or `x` is needed. The final constant is uniform and positive even when `C+x` is negative.

The scope matches the reports: these modules prove the actual normalized local application. Obtaining the common localization radius and density class from an arbitrary original configuration, paying those population losses, and absorbing them into the final unrestricted estimate remain the separate globalization stage. The local theorem explicitly treats positive population; an unrestricted wrapper must handle the zero-population case separately.

No reviewed source or shared registry was edited.
