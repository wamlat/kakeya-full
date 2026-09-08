# Occupancy selection formalization

`OccupancySelection.lean` compiles with Lean 4.33.1 and the pinned mathlib. Its 14 theorems have no `sorry`, custom axiom, or assumed analytic result. Every printed theorem dependency is contained in the standard Lean logical axioms `propext`, `Classical.choice`, and `Quot.sound`. The build also produced `.lake/build/lib/lean/OccupancySelection.olean`; the complete compiler/axiom output is `occupancy_selection_compile.log`.

## Constructed steps

The module constructs the high-occupancy filter from actual measurable cell weights, bounds its removal loss per tube by `lo * V * K`, selects a dyadic occupancy class by the actual sum of tube-incidence measures, prunes tubes below half their average remaining mass, selects a dyadic tube-mass class, and chooses actual cell subsets with one common positive integer cardinality. No favorable class, surviving family, or equal-cardinality subset is assumed.

Let `M` be the original tube count, `Bocc = Jocc + 1` the number of occupancy classes, `Btube = Jtube + 1` the number of tube-mass classes, `W` the incidence mass surviving the cutoff, `upper` a uniform per-tube mass upper bound, and `v` the selected occupancy mass per cell. `CommonIntegerSelection` records actual selected cells/tubes and shadings and proves

- each selected cell has ambient-union mass in `[v, 2v)`;
- the common integer count is positive and at least `W / (4 M Bocc v)`;
- `W ≤ 2 Bocc Btube upper * number_selected_tubes`;
- the selected original measurable tube masses lie in one common dyadic interval;
- every chosen shading cell has positive intersection measure with its own original tube shading;
- `v * number_of_cells_in_the_discrete_union ≤ measure_of_original_union`.

The stronger `high_occupancy_integer_selection` starts with actual original shadings. A required mass `base>0`, a positive-cell count bound `K`, and `lo * V * K ≤ base/2` imply that every tube retains at least `base/2` under the actual filter. The theorem then constructs all classes and common integer shadings. Root's separate `GridCells.positive_tube_cell_count` can supply the geometric count bound.

## Explicit scope boundaries

Class coverage assumptions are quantitative finite inequalities: `1 ≤ lo*2^Jocc` and `upper ≤ (base/(4Bocc))*2^Jtube`. `finite_class_budgets` proves that finite budgets always exist from positive `lo` and `base`; it does **not** identify these unspecified budgets with logarithmic uniform constants. Any uniform scale-loss theorem must bound their growth separately.

This module works for a finite disjoint measurable CellSystem with positive common cell volume. It neither assumes nor proves the new analytic Kakeya estimate. Actual Euclidean grid geometry and subfamily cap preservation are application steps in other modules.

A common count can exceed `1/δ` by a geometric constant. This module does not silently assert the density is at most one. Its optional `uniform_integer_trim_capped` constructs further subsets of cardinality at most a supplied positive integer `N`, retaining the explicit lower bound `min(original_lower_bound,N)`. `capped_density_bounds` then proves `0 < K/N ≤ 1`. Root's separate DensityNormalization supplies the stronger constant-factor normalization at noninteger `1/δ`.
