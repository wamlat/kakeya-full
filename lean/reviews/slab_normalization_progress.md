# Common grid-compatible slab normalization

`formalization/SlabNormalization.lean` contains 18 proved theorems and four definitions. It closes the common vertical-slab normalization adapter after `SelectedFiberSlab`, including arbitrary positive real mesh size rather than assuming `1/delta` is an integer.

## One exact shift per original group

For the original unit-slab index `j`, define the integer `q=floor(j/delta)` and physical shift `eta=delta q`. Every line and cell in a fixed original `(pivotLabel,j)` group uses this same shift. The vertical cell label changes by `z(0) -> z(0)-q`, and all horizontal labels remain literally unchanged. The corresponding Euclidean point shift is subtraction of `cons eta 0`.

The module proves exact grid compatibility, distance preservation, unchanged horizontal coordinates, and

`eta ≤ j < eta+delta`.

Thus a cell center originally in `[j,j+1)` moves into `[0,1+delta)`. All of these translation results hold for every `delta>0`. No floor error is discarded.

The graph identity is exact:

`shift(graphPoint a v t) = graphPoint (a+eta v) v (t-eta)`.

Slopes and graph directions are unchanged. An actual original graph-incidence error `width delta` and center-slab membership imply the shifted parameter range `[-(width+1)delta, 1+(width+1)delta]`, with the same physical incidence error.

`shifted_card`, `shifted_union`, and `shifted_union_card` prove exact per-line and whole-group cardinality preservation before unit-segment normalization. The union equality uses one common shift. No independent translation of each line inside a common union occurs.

## Genuine unit-tube normalization

`normalize_common_slab` invokes the actual `LiftSegments.normalize_graph_family` construction on the commonly shifted graph shadings. A nonempty retained cell per line and a bound on its actual horizontal coordinate derive a uniform translated intercept bound. This avoids introducing the potentially large slab index into the normalized geometry.

The concrete theorem `normalize_selected_group` specializes to the actual selected `LabeledPair` lifts and one original group `(pivotCell,slabIndex)`. Its inputs are the chosen nonempty actual cell sets `S_i`, inclusion in each line's actual `liftedCells`, common center-slab membership, bounded original angle vertices, actual common reference-pivot labels and intermediate-label projection closeness.

It constructs an actual unit-tube family `G` and proves:

- direction `graphDirection(referenceCoefficient_i • secondDirection_i)` for every tube;
- each `G.shade_i` is a subset of the commonly shifted `S_i`;
- `#G.shade_i ≥ #S_i/3`;
- actual admissibility width `3(k+1)/2+2`;
- actual tube-base bound `R+6+3(k+1)/2` when original angle vertices have norm at most `R`;
- the normalized union is contained in the commonly shifted original group union, and its cardinality is at most the original group union cardinality.

The factor three is the proved unit-piece count `ceil(1+1)+1`, because legal reference slopes have norm at most one. All normalization constants are independent of kappa, the slab index, scale, line count and shading count. The bounded-geometry/unit-tube step uses the source scale range `0<delta≤1`; exact translation itself only requires positive delta.

## Original pivot grouping and residual

`reference_pivot_residual` derives the actual slope residual

`norm(v_i - (cellCenter delta pivot - cellCenter delta intermediateLabel_i)) ≤ (widthOriginal+k/2)delta`

from the legal exact pivot identity, actual pivot rounding and actual intermediate-label projection closeness. The selected-group theorem returns this bound against the original common pivot and the original intermediate cell labels. Those horizontal labels and coordinates are never relabeled by the vertical shift. There is no assumed lifted cap bound or direction separation in this module; the existing fixed-pivot cap/color theorems can use these actual slopes, labels and residuals.

The module works within one original pivot/slab group and does not sum over groups. Therefore no number-of-groups factor is introduced or concealed. The later global analytic/grouping assembly remains separate.

## Verification

Compilation and `.olean` generation pass without warnings. Seven main theorem axiom reports use only `propext`, `Classical.choice` and `Quot.sound`; no `sorry`, `admit` or custom axiom is present. Compiler output: `audit_work/slab_normalization_compile.log`.
