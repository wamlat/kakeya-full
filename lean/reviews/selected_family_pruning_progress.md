# Actual normalized selected families and uniform pruning

All three modules are clean-compiled, built, fully source-audited, and frozen. They contain 24 theorems, 12 definitions and one proof-bearing structure. Every one of the 37 named declarations passed a fresh audit with an exact source-prefix check; there are no errors or warnings, and the exact axiom union is `propext`, `Classical.choice`, `Quot.sound`.

The bridge consists of `SelectedBaseFamilies.lean`, `SelectedColoredFamilies.lean`, and `SelectedFamilyPruning.lean`. These construct the previously missing actual normalized families and common-color incidence data from the selected original output lines, then instantiate the analytic grouped pruning theorem.

## Actual data and uniform quantifiers

The main theorem is `SelectedFamilyPruning.constructed_pruning`. It assumes a normalized `DiscreteEstimate (k+2) d d' p`, p≥1, d≥0, a positive loss eps, and fixed original width and bounded-base radius. Its positive analytic constant c is chosen before every original M, δ, λ, κ, F, H, SampleSystem S, Selection P, actual simultaneous LineData D, and spatial coefficient C_ball.

After c is fixed, the actual-data inputs are 0<δ≤1, C_ball≥1, original F.Bounded, and the literal all-radius ball count on the original `F.unionCells` labels at the normalized mesh δ_n=δ/(1+2width). There is no presumed admissibility of original F at δ_n. `PrunedScaleTransport` supplies precisely the intended mesh transport.

The theorem constructs a family collection A, one family for every actually used original pivot/slab group, and an actual retained incidence set T. It derives all unit-tube/shading, geometry, cap, color, population and incidence prerequisites internally. The public theorem has no independent normalized-family, cap-count, separation, support-count, retained-mass, or upper-energy premise.

## Exact normalization and population

Each original selected output belongs to one finite base group: its unchanged pivot label and its own selected original unit slab. The full normalized family in that group is constructed using `SlabNormalization.normalize_selected_group` on the actual reference pair, actual raw pair image, and actual K selected cells from `SelectedOutputSlabs`.

Every normalized shading is a subset of its own original selected cells shifted by that group's one common integral vertical translation. Its cardinality is at least K/3, and it is nonempty. The original output index is recovered by the exact finite grouping equivalence, so the global maps `tube` and `shading` retain every original q exactly once.

The color is computed from q's unchanged intermediate grid label with one common modulus. The final colored group is exactly `(original pivot, original slab, computed color)`. Its total line population equals Q, and its literal normalized incidence set S has cardinality at least KQ/3. There is no selected-color pigeonhole and no number-of-base-groups factor.

## Constants independently rechecked

Write n=k+1 for the original ambient dimension and w for the original physical width. The original vertex bound is `max(0,R)+1+w`. The selected graph slopes have norm at most one. At mesh δ_n the intermediate projection error is 2wδ_n and the pivot-label rounding error is at most nδ_n/2. Consequently:

- the graph slope residual is C_error δ_n with C_error=2w+n/2;
- a cap of graph directions of radius r≥δ_n maps to a ball of original intermediate labels of radius `(16+2C_error)r`;
- the actual cap coefficient is `C_ball*(16+2C_error)^d`;
- the residue modulus is `ceil(2C_error+1)` and the exact palette cardinality J is that modulus to power n;
- equal colors in a fixed original pivot/slab group give separation δ_n/8;
- the normalized tube width is `3(n+1)/2+2`;
- the normalized base radius is `max(1, R_vertex+6+3(n+1)/2)`.

The factor 16 comes from the graph-chart inverse constant 8 and the 2r distance between two directions in one cap. The two rounding residuals contribute 2C_error r. The modulus leaves at least δ_n of label separation after those two errors, yielding δ_n/8 in direction. The unit-segment covering count is exactly three, explaining K/3. The horizontal bound on an actual retained point controls the shifted intercept, so the slab index never enters the normalized radius. None of these constants depends on κ, Q, or the slab index.

The spatial count is required at all radii because `(16+2C_error)r` can exceed one; the wrapper does not silently use only small-radius pruning there.

## Exact pruning output

With rho equal to `SelectedOutputDensity.rho` of the constructed actual shadings and A_cap the actual cap coefficient above, the retained T satisfies |T|>|S|/2 and

`Σ_position degree(T)^2 ≤ [2^(p+1) J (1/δ_n) / (c A_cap^(-1) δ_n^(d-d'+eps) rho^(p-1))] |T|`.

Positions retain the literal original pivot/slab label and normalized cell. The expression is the exact input of `SelectedOutputClosing.retained_closing`, including the exact palette cardinality and density definition.

This completes the constructed-family/pruning interface. The normalized analytic estimate remains the explicitly stated input, supplied at the desired exponents by the separate seed/iteration arguments. The closing-energy composition and original marked/pruned configuration assembly are separate modules under active development.
