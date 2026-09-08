# Independent localization and occupancy review

Reviewed `Localization.lean`, `MeasurableLocalization.lean`, and `MeasurableOccupancy.lean` against the relevant localization and occupancy interfaces in the combined PDF. No incorrect theorem statement, hidden two-ends premise, circular localization premise, or finite-measure error was found.

## Localization modules

Both modules select the smallest dyadic radius carrying at least `R^alpha` of the original mass; they do not assume the selected radius or a localized two-ends estimate. The top-scale witness follows from the explicit unit-ball cover hypothesis. `dyadic_round` rounds every radius in `[2^(−J),1]` upward with factor at most two. Minimality handles `2r<R`, while ordinary mass monotonicity handles `2r≥R`. This correctly proves the factor `2^alpha (r/R)^alpha` at every radius above the bottom scale, not merely at dyadic radii.

The finite version explicitly assumes nonnegative weights. The measure version explicitly assumes measurability and finite measure of the shading, but **does not require the ambient measure to be finite**. Its monotonicity steps carry the necessary finite-measure hypotheses, so it applies to finite-measure subsets of a Lebesgue space. Closed-ball restrictions are measurable in the stated metric/Borel setting. Zero mass and `alpha=0` are valid harmless cases; applying these results to a positive-density theorem still requires the corresponding positive-mass input elsewhere.

The unit-ball cover is stronger than an arbitrary bounded-region statement; using the manuscript's fixed-scale normalization is a separate application step. The constructions use classical existence/choice, so “constructive” here means a proved mathematical selection, not an executable algorithm on an encoded measurable set.

**Coverage boundary:** these are single-shading localization theorems. They do not yet prove the common-radius/common-density family pigeonholing with its `L^(−2)` tube-retention factor, or the tube-geometry upper bound on localized mass. Those assertions must not be credited to the current modules.

## Measurable occupancy module

`CellSystem` requires a finite, measurable, pairwise-disjoint family of finite-measure cells. Exact disjointness is an explicit assumption; a Euclidean implementation can use half-open grid cells, but the module does not construct them or silently identify overlapping closed cubes with a partition.

The exact mass-decomposition theorem requires the shading to lie in the covered cells. The selected-class identity does not need that global cover, because it computes an intersection with the selected cells. All finite-measure requirements in `Measure.real` monotonicity are checked through the finite cell cover or finite individual cells.

The count/volume inequalities point in the correct directions:

- lower union occupancy gives `v #selected ≤ original union volume`;
- upper ambient-union occupancy gives `restricted shading mass ≤ v #positive shading incidences`;
- zero-volume intersections contribute exactly zero even if nonempty as sets;
- normalized occupancies lie in `[0,1]` under the explicitly positive common cell volume;
- low-occupancy loss additionally requires an explicit bound on the number of positive cells meeting a tube.

The ambient union need not itself be assumed measurable in the monotonicity inequalities; its intersections are finite because they lie in a finite-measure cell, and outer-measure monotonicity suffices. Actual measurable union applications have stronger hypotheses anyway.

**Coverage boundary:** no common dyadic occupancy class, tube-density class, or integer-count trimming is selected in this file. The cell-count bound per tube remains an application hypothesis, and the exact measurable-grid realization is still separate. These are meaningful measure-theoretic interfaces rather than a formal proof of the entire measurable conversion.
