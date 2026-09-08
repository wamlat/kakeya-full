# Independent review of the measurable position reduction

Read-only review of the actual constructions in `MeasurableUnitPartition.lean` and `MaximalPositionReduction.lean`. No substantive mathematical defect found. Both sources were reviewed at their final frozen, clean-built versions. The final adapter changes only make unfoldings, casts and division manipulations explicit; they do not alter the mathematical assumptions or conclusions.

Every actual unit-tube carrier at delta≤1 lies within distance two of its base. The half-open unit-grid labels intersecting such a carrier therefore belong to an explicitly bounded finite candidate set with a count depending only on ambient dimension. On every positive measurable shading, the largest actual candidate intersection retains at least the reciprocal of this fixed count. Positive retained measure supplies an actual point witnessing bounded distance of the base from the selected cell center. No occupied-grid counting premise is assumed.

The partition keeps every original tube, assigning it to one actual cell. Its selected full shading is the literal original shading intersected with that same cell. Group unions are subsets of distinct half-open OLD cells, so their original measurable unions are disjoint. The sum of their measures is at most the original full union measure. Finite measure is established from actual carrier finiteness; no position bound is needed for this step.

The adapter translates all tubes and selected shadings of one group by its common cell center. The unit scale and zero longitudinal offset give an exact carrier image, with unchanged direction, width and length. Exact Lebesgue translation invariance identifies both the full tube volumes and selected union measure. Bases become uniformly bounded by the dimension-only radius obtained in the partition. Direction separation is inherited under the injective group reindexing.

The selected density is lambda/K, with K the fixed dimension-only candidate count. It is positive and at most one. The given bounded-position estimate is invoked with the same fixed radius, separation and epsilon for every group. The sum of actual translated tube volumes equals the original sum, since every original tube appears once. Summation then uses the OLD disjoint union bound, never any supposed disjointness between independently translated groups.

Consequently the fixed coefficient c/K^d yields the literal arbitrary-position `MaximalShading.Estimate n d`, with no original bounded-position, cap, grid, grouping, or population premise. This argument is valid for every real d; no sign test on d is required because the density scaling is an exact positive-base power identity.

Frozen partition SHA-256: `eba0ef701d0a714dfc0d46c2a1c2a0786b0d39ae65d2305ed34e27b09220bf2a`.

Frozen adapter SHA-256: `6fc8fce648451195825507e1bb3e00e242cc663b4e07985ba4f22f7fdab30ace`.
