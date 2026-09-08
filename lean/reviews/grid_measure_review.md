# Independent review: TubeLocalCount and GridCells

Reviewed the current `TubeLocalCount.lean` and `GridCells.lean`, including bounded-set finite coverage and positive-measure tube-cell counting, after completion of ProjectiveGeometry. No norm, scale, measure-normalization or finite-cover error was found. No edits were made.

## TubeLocalCount

- The axis uses a direction with Euclidean norm exactly1, so parameter differences equal physical axis distances. The parameter gap2*(r+width*delta) follows from two center-to-axis errors and two center-to-ball-center distances.
- Fixing one occupied cell gives an axis interval of total length4*(r+width*delta). Its endpoints need not belong to the original unit segment; this is harmless because the theorem uses the unrestricted axis and an arbitrary endpoint segment as a containing set. The actual shaded points still have witnesses in the original [0,1] segment.
- The empty-cell case is handled separately. The nonempty case picks an existing cell before choosing its axis parameter.
- The exact bound uses `ceil(4*(r+width*delta)/delta)+1`. At r≥delta, it is correctly bounded by `(6+4*width)*(r/delta)`; width≥0 and delta>0 are explicit. This gives the required linear radius scaling, not an ambient-power ball bound.

## GridCells: geometry and normalization

- Cells are truly centered at `delta*z` with side length delta, using lower-closed upper-open coordinate intervals. For delta>0 the label `floor(x_i/delta+1/2)` matches precisely these boundary conventions, including points on faces. It gives both coverage and pairwise disjointness without a boundary-measure exception.
- The exact volume is `(ENNReal.ofReal delta)^k`. `PiLp.volume_preserving_ofLp` identifies the Euclidean-space volume with ordinary coordinate product Lebesgue measure, so no Jacobian, sqrt(k), or missing normalization factor is introduced. The real-valued result assumes delta≥0 and returns exactly delta^k.
- The all-real-delta volume statement remains valid even for nonpositive delta: reversed coordinate intervals are empty in positive dimension; in dimension0 the product space is a point and the empty product is1. Later coverage and labeling use delta>0 explicitly.
- `cell_center_distance` uses a deliberately loose k*delta/2 bound, obtained by summing coordinate errors. This is a valid bound in the actual Euclidean norm. The lack of a separate delta>0 premise is harmless: the premise that a point belongs to such a cell already excludes negative width when k>0; the k=0 case gives distance0.
- Touching a tube enlarges its admissible center width from width to width+k/2, exactly as the triangle inequality requires. The enlargement is fixed before scale variation and therefore allowed by the normalization model.

## Finite coverage and positive measure

- `touching_bounded_set_label` constructs an explicit finite integer box containing every cell meeting a bounded set. Its radius accounts for both the set's radius R and the center-to-cell error. It does not assume a finite touching-cell count.
- `bounded_set_covered` uses the unique actual label of each point and the finite box's `equivFin`. It constructs membership in the finite cell system and does not drop boundary points. Measurability of the bounded set is unnecessary for this set-theoretic coverage theorem, so its statement is slightly stronger than its commentary.
- `positive_tube_cell_count` requires only that the shading lie inside the physical tube. Positive real measure implies the cell intersection is nonempty, after which the independently proved geometric tube-grid bound applies. No desired incidence-count estimate is a premise.
- `.real` sends infinite ENNReal measure to0, but that is not exploited to infer a false result here. Each concrete cell has finite measure, and any intersection with it is bounded in measure by that cell. The finite `CellSystem` also explicitly stores finiteness. Any later passage from real measure to total shading measure should retain those finiteness/coverage hypotheses.

## Remaining claims not provided by these files

These results supply the elementary actual-grid geometry and finite measure partition. They do not yet identify the paper's tube-volume normalization `|T| asymptotic delta^(k-1)`, establish arbitrary shading-to-discrete density normalization, prove fractional directional-cap preservation after rescaling, or supply the new analytic pivot estimate. Those need their own arguments. No blocking defect was found in the reviewed code.
