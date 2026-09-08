# Heavy-cell incidence bounds and simultaneous spatial pruning

Both new modules compile cleanly with Lean 4.33.1 and the pinned mathlib checkout. `HeavyIncidence.lean` has 9 theorems; `PrunedIncidence.lean` has 4. Their main theorems' only axioms are `propext`, `Classical.choice`, and `Quot.sound`. There are no placeholder proofs or custom axioms.

## HeavyIncidence

The actual heavy coarse labels are the labels whose E-fiber cardinality strictly exceeds `L (r/δ)^d`. Actual tube shadings are filtered by membership in those labels. If the deleted incidence exceeds `eta λ M`, the proof constructs the actual set of tubes with heavy shading mass at least `eta λ/2`; there are at least `eta M/4` of them. It injectively reindexes those tubes and preserves their actual cap, location and incidence geometry. Original direction separation is not required.

The already verified actual coarse-family estimate and disjoint heavy E-fibers then force

`|E| ≥ [c/(4·2^p)] L A⁻¹ δ^(m−d) r^eps eta^(p+1) λ^p M`.

The exact scalar identity, including every exponent and selection constant, is proved. From it, `discrete_heavy_mass_bound` obtains a fixed positive K from the base `DiscreteEstimate`, before all configurations and testing scales. For every δ≤r≤1, if

`L ≥ K |E| A δ^(d−m−eps) eta^(-(p+1)) λ^(-p)/M`,

then the actual total heavy shading mass is at most `eta λ M`. The same L works at all scales. The zero-tube and zero-E cases are handled explicitly. This result works for any nonnegative cap exponent m and p≥1; d need not be nonnegative until the spatial ball extension is used.

## PrunedIncidence

The new family is constructed by intersecting every original shading with `BallPruning.survivors`. For each deleted incidence, the proof finds a tested scale where its actual coarse fiber is heavy. A finite union count bounds total deletion by the sum of the scale losses. No independence or disjointness of deletion events is assumed.

`discrete_spatial_pruning` derives a uniform constant K from the base estimate and constructs J with `J ≤ log(1/δ)/log 2`. It uses `eta=1/(2(J+1))` and

`L=max(1, K |E| A δ^(d−m−eps) eta^(-(p+1)) λ^(-p)/M)`.

For original shadings with normalized mass between λ and 2λ, the actual survivor family keeps the same tubes, uses subsets of the original shadings, and retains total normalized incidence at least `λ M/2`. Its actual union satisfies the physical ball bound

`#(union ∩ ball(x,rho)) ≤ coverConstant(k+1,1) 2^d L (rho/δ)^d`

for every center and every δ≤rho≤1. Constants precede the actual family, scale, cap coefficient and density. Empty families are included.

## Remaining downstream interfaces

These results are conditional consequences of the base discrete estimate; they do not prove the lifted induction step by themselves. The survivor family has a cumulative mass guarantee. It does not claim every individual surviving shading still has density comparable to λ; empty or small surviving shadings remain possible. Any downstream construction needing per-tube comparability must perform a further actual tube/density selection or use the proved cumulative estimate.

The displayed J-dependent cutoff is explicit. Its logarithmic factor has not been absorbed into a new uniform scale loss within `PrunedIncidence`; that is a separate scalar step if a downstream statement requires precisely the manuscript's power-loss notation. The module exports balls through radius one. Extending to all larger radii uses the existing bounded-region interface in `BallPruning.dyadic_all_ball_bound`.

The endpoint/output selection, construction and transport of lifted incidence records, common pivot/slab witnesses, and closing endpoint-triple geometry remain separate downstream geometric interfaces. Neither new module assumes these witnesses or identifies them with already constructed data without proof. Root independently reviewed the heavy-cell definitions, selection and calibration and found no issue before this checkpoint.
