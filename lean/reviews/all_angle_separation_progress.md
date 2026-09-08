# Fixed-separation normalization of the all-angle pivot

`AllAngleSeparation.lean` is frozen and clean-built. SHA-256: `9d36ee3a6ff816e181da96501144e7b0eeea11cb688f77426ff0fdd17258de39`. The exact full-source audit rechecked all four theorems; each depends only on `propext`, `Classical.choice`, and `Quot.sound`. There are no new custom axioms, admitted proofs, compiler warnings, or supplied coloring/population premises. This module is subsequent work, outside the frozen checkpoint 16 snapshot.

`all_scales` extends `AllAnglePivot.all_scales` to original separation `sigma * delta` for any fixed positive `sigma`. It invokes the actual projective-packing/greedy-coloring construction in `SeparationColoring`. The number of colors is the fixed integer

`P = paletteSize (ambient−1) sigma = ceil(packingConstant(ambient−1) * (1/min(sigma,1))^(ambient−1)) + 1`.

The new `exists_large_color` theorem derives a largest actual class with `M ≤ P * M_class` from the exact color partition. The new `class_union_subset` theorem identifies its union as a subset of the original finite cell union. The selected class is injectively reindexed, and each tube and its **complete original shading** are unchanged. Admissibility, comparability, bounded bases, and every full two-ends ball inequality therefore pass literally; real-cap bounds pass without an additional coefficient loss. The proved unit-separation theorem is applied to this actual class, and the final coefficient is its uniform coefficient divided by `P`.

The main coefficient is fixed before the family, scale, density, cap coefficient, and population. No logarithm, scale, density, or tube-count term occurs in the palette. Empty populations are covered without needing a nonempty original class: the palette itself is positive, and the original theorem already handles empty families.

The convenient downstream API is

`configuration_estimate hbase hlift hm hmn hp hd hq hD geom B alpha eps hB halpha heps hmargin`.

It returns a positive uniform coefficient for every actual `ShadedConfiguration (k+2) geom m`, assuming only its original full two-ends inequality in addition to the stated analytic base/lift and parameter conditions. The arbitrary normalization `geom` supplies width, separation, and base-radius constants before configurations. The conclusion has the exact original form

`c * A⁻¹ * delta^(m − pivotSet(m,d') + eps) * lambda^pivotDensity(pExp,qExp) * M ≤ #unionCells`.

The remaining analytic boundary is unchanged: full two ends is still required, along with the two explicit analytic estimates, `pivotSet < m`, and the sparse-density margin. The finite agent is wrapping this result in the named `TwoEndsDiscreteEstimate` interface for the next spatial-localization stage. No frozen/shared module was edited.
