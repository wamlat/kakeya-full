# Original-grid counts of actual spatial pieces

New module: `formalization/SpatialGridPopulation.lean`. It imports the frozen `SpatialMarkedGroups` and `AngularRestrictedMeasurable`; no existing source, lakefile or verifier was edited.

`boxCells F lab q` is the actual old-cell union of the injectively reindexed label fiber. `box_full_union` proves exact equality, including half-open cell boundaries:

`union_i Full (GridMarked.shading F delta W) lab q i = normalizedSet W (cellUnion delta (boxCells F lab q))`.

The physical spatial-overlap theorem was already proved from tube carriers and actual base labels. `all_box_counts` applies its integrated bound to these exact unions. Both sides have the SAME positive factor `delta^(k+1)/W^(k+1)`, which is cancelled to obtain

`sum_q card(boxCells_q) <= overlapConstant(k,width,angular)*card(F.unionCells)`.

There is no statement that the sampled cubes, or the pullbacks of sampled cubes, have bounded overlap. `box_counts` retains any actual subcollection with the same bound, so no preferred box is selected.

The module then specializes to the exact whole-Ref sets of `AngularRestrictedMeasurable`. `refinedLabel` uses the actual normalized tube bases and the original angular center; `refinedCells` is the corresponding OLD grid union. `refined_full_union` is the exact measurable identity for those existing Ref sets. `refined_box_counts` proves, without a caller-supplied overlap or count hypothesis,

`sum_q card(refinedCells_q) <= overlapConstant(k,1,3)*card((P.family g).unionCells)`.

Here carrier width one comes from the checked whole-cell common normalization, angular width three comes from the actual original angular group, and the refined union is contained in the original restricted angular-piece union by V.union_subset.

`sum_refined_box_counts` composes this result with the actual `AngularPiecePopulation.sum_old_unions` theorem. It yields

`sum_g sum_q card(refinedCells_gq) <= overlapConstant(k,1,3)*(2*tau^(-beta)*card(F_original.unionCells))`.

The sum runs over every actually kept angular group and any retained spatial subcollection. `sum_good_refined_box_counts` instantiates ALL literal `SpatialMarkedGroups.good` boxes and discharges the subcollection condition internally. Its eta/mass parameters merely define that actual filter; it makes no unproved mass-normalization assertion.

Scope: this closes the ORIGINAL GRID overlap boundary requested. It does not yet instantiate and sum the later low/high sampling estimates. A subsequent call to AnisotropicSamplingInput must also establish its dimensionless density <=1: V.density<=2*originalLambda and widthFactor>=1 alone do not imply this in every small ambient dimension. One must use an actual denominator lower bound in the recursive dimension range, or an additional fixed common homothety. This module neither clamps that density nor assumes the conclusion.

Verification: clean Lean 4.33.1 `.olean` build, no warnings. Fresh complete-source audit checks all 11 declarations (eight theorems, three definitions), with exact source-prefix match and only `propext`, `Classical.choice`, `Quot.sound`. Audit files: `spatial_grid_population_full_source_audit.lean` and `.log`. Source SHA-256: `57b16d013dfb0eb95326ca346beccac56811d54c9c0d1553f5370b4c32fb9731`.
