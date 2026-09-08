# Separate mathematical review of the fractional seed

No mathematical defect was found in the reviewed seed chain. The final statement is an unconditional theorem of the actual finite tube/grid predicate `RealCapEstimate`, with its required uniform quantifiers. This conclusion concerns the fractional seed; it does not establish the manuscript's later pivot estimate or final endpoint unconditionally.

## Scope and verification

Read the statements and proof bodies of FiniteGridLocalization, FiniteLocalizedFamily, LocalizedSeedNormalization, LocalizedSeedApplication, CoveredSeed, SeedGlobalizationAlgebra, and FractionalSeed. Also reviewed the directly relevant LocalizedDirectionThinning and SeedCoverNormalization bridges and checked the used interfaces/proofs in FamilyLocalization, UniformLocalization, LocalizedGridTubes, Rescaling, GridTwoEnds, AngularSeedEstimate, and AngularSeedBound. Previously frozen angular/hairbrush internals were consulted at their proved interfaces rather than all independently re-proved during this bounded review.

Independently compared the nine current seed-module sources to the prefixes of their full-source audit files. Every prefix was exact. Their 51 theorem-audit outputs contained no errors, warnings, or `sorryAx`; the audited dependency sets are the standard foundational axioms. No seed source was edited. The forthcoming root isolated build/environment audit remains a separate verification layer.

## Exact theorem and uniformity

`FractionalSeed.fractional_real_cap_seed` has only `m>3` as its mathematical premise and proves `RealCapEstimate m d d`, where d=(m+3)/2. Unfolding the actual Configurations predicate gives:

For every adequate integer ambient dimension n with m≤n−1, every fixed geometric normalization, and every ε>0, there is c>0 such that every actual normalized finite tube/grid configuration satisfies

c A^(-1) δ^(m−d+ε) λ^d M ≤ |unionCells|.

The positive c is chosen before δ, λ, A, M, tubes, shadings, localization radii, and localization centers. In the final proof, the logarithmic absorption constants, α, β, the initial cover factor, and all local-seed constants are selected before `intro F`. The intermediate `covered_seed` and `localized_seed` constants likewise precede all families and their variable radii/densities.

There is no real-cap estimate, analytic seed, two-ends property, preselected localization, prescribed direction subfamily, or union-count inequality assumed in the final theorem. The intermediate two-ends premise is discharged by actual finite localization.

## Localization and density classes

The grid-center map is injective when δ>0. Thus passing to physical centers and back preserves each finite cardinality exactly. `restrictCells` retains original labels rather than covering or enlarging their cells.

The common-radius selection retains at least M/(J+1) tubes by an actual finite weighted-class selection with tube weights one. Comparable positive original density ensures every original tube shading is nonempty. Each retained shading has at least ρ^α of its original mass and physical ball tests at every center and every radius δ≤r≤ρ.

The additional density-class budget depends on the ratio (2λ/δ)/(ρ^α λ/δ)=2/ρ^α. The original λ cancels exactly. Consequently the combined count loss is at most (α+3) L(δ)^2, uniformly in λ. The selected family is injectively reindexed from the original indices, its shadings are actual original subsets, and its union is an actual subset of the old union.

## Coarse direction selection and cap coefficient

`cap_bound_smaller_scale` is valid in both radius branches. Above the old mesh, the denominator change only enlarges the permitted right side. Below the old mesh, the old endpoint test gives count≤A, which is bounded by A(u/δ_new)^m since u≥δ_new and m≥0.

`thin_to_scale` first applies the proved full cap hierarchy at max(old mesh,target mesh), then selects an actual largest color class from a fixed palette. It retains COMPLETE localized shadings on injectively chosen original indices. The target-separated family has a cap coefficient depending only on the ambient index and m. No original separation is needed for this construction; cap control already limits multiplicities.

At common dilation L=Kρ, the retained population is at least Mρ^m/(T A). This is the sole occurrence of the original inverse A loss. The two-ends seed is applied with the NEW fixed cap coefficient, so a second original A^(-1) is not accidentally paid or suppressed.

## Physical normalization and original union

The dilation constant K is at least both the short-axis interval coefficient and the actual local tube-ball population coefficient. Therefore every localized shading fits a genuine unit tube after dilation, and its actual comparable density s/(Kρ) is at most one by geometry. This density condition is derived rather than clamped or assumed.

All tubes use one spatial homothety about the same zero-grid origin. Different per-tube axis interval endpoints only choose the bases of unit carriers along the transformed axes; they do not translate the shading points separately. The finite label map is globally injective, so union cardinality is exact under the common rescaling and can only decrease under tube selection. The proof does not sum separately normalized unions or assume overlap of unrelated coordinate systems.

No bounded-base premise is needed by the applied AngularSeedEstimate theorem. Thus arbitrary localization centers do not require an omitted spatial clustering argument. `GridTwoEnds.rescaled_two_ends` handles radii whose inverse image exceeds ρ by the total-cardinality bound, with the fixed coefficient B K^α; no density-dependent normalization constant is hidden there.

## Power accounting

Writing x=(m−3)/2+η, the exact normalization identity contributes

δ^x s² ρ^(m−2−x) M/A.

Since ρ≤1 and m−2−x=(m−1)/2−η, replacing this radius power by ρ^((m−1)/2) weakens the lower bound in the correct direction.

The local tube count gives s≤Cρ, while retained mass gives s≥ρ^α λ. Thus λ≤Cρ^(1−α). For d=(m+3)/2≥2 and 0≤α<1, the exact algebra proves

C^(-q) λ^(d/(1−α)) ≤ s² ρ^(d−2),

where q=(d−2+2α)/(1−α)≥0. Multiplying by the actual retained tube count gives the covered-family estimate with density exponent d/(1−α), not an unproved stronger density exponent.

The final choice η=ε/3 and α=η/(d+η) gives d/(1−α)=d+η exactly. For nonempty finite integer shadings, comparability proves λ≥δ/2. The inequality is used only in that finite setting, after the shared cover homothety, and the empty-family case is separate. It pays for one η of density error. The two logarithms pay for another η of scale error. Together with the local seed's η, the total error is exactly 3η=ε.

Finally, the initial cover homothety scales both δ and λ by the same fixed C. Their powers combine to C^(-(m+ε)), independent of the configuration. The final density power is exactly d and the scale exponent exactly m−d+ε.

## Dimension and interpretation boundaries

The ambient family theorem is proved in every dimension of the form k+2. The final RealCapEstimate theorem handles dimensions zero and one by incompatibility with m>3 and m≤n−1, and all other dimensions by that family theorem. It introduces no integrality assumption on m and no missing adequate-dimension case.

The result is the unrestricted finite-grid fractional seed corresponding to the manuscript's Section 4 seed. The finite lower bound λ≥δ/2 must not be presented as a statement about arbitrary measurable shadings. A separate interface would be needed for an arbitrary-measurable endpoint with exactly the same density power if its proof tried to use that finite fact. The existing SeededEndpoint wrappers remain conditional on the explicitly stated pivot premise, as the scalar report correctly says.
