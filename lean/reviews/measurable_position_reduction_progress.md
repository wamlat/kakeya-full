# Actual arbitrary-position measurable reduction

The bounded-region convention in the manuscript's formula (1.1) is now removed constructively. Two new frozen modules prove

`MaximalPositionReduction.bounded_to_unbounded : MaximalShading.BoundedEstimate n d → MaximalShading.Estimate n d`.

The conclusion is the literal cap-free estimate with arbitrary tube positions, arbitrary measurable shadings inside their unit delta-tubes, fixed positive direction-separation coefficient, and the sum of **actual tube volumes**. It has no input spatial partition, bounded-base hypothesis, cap condition, two-ends condition, selected-mass premise, or volume-comparability premise. The only analytic hypothesis is the corresponding bounded-position estimate. The theorem works for every real `d`; it needs no added sign restriction on that exponent.

`MeasurableUnitPartition` constructs the spatial partition from the actual measurable shadings. For every unit tube with `delta≤1`, each carrier point is within distance two of its base. The center of the unit-grid cell containing such a point is therefore within `2+n/2` of the base. An explicit integer box covers all these cell labels, with dimension-only cardinality

`K(n) = (2*(ceil(2+n/2)+1)+1)^n`.

The proof chooses a largest actual cell-intersection mass on every tube. Exact finite additivity over the disjoint half-open cells gives retained mass at least the original shading mass divided by `K(n)`. Positive original shading mass follows from the requested positive density and the proved positive actual tube volume. Thus the selected cell contains a real point of the original tube, and the original base is within `2+n/2` of its center. Every tube survives in precisely one assigned cell.

The selected sets are the literal intersections of the old shadings with their assigned unit cells. Group unions lie inside their corresponding old cells, so different groups are disjoint. Their actual measures sum to at most the original full union measure. This is an exact measurable-set argument; no sampled-cell count, informal bounded overlap, or comparison of separately transformed physical unions is used.

`MaximalPositionReduction` translates each entire group by its one cell-center vector. It proves that the translated full unit-tube carrier is exactly the image of the original carrier. Consequently each actual tube volume, each selected shading volume, and each group-union volume are preserved. Bases in every translated group obey the same fixed radius `2+n/2`, directions and separation are unchanged, and the normalized shading density is exactly the common lower parameter `lambda/K(n)`. The auxiliary finite-grid shading field is unused by the measurable predicates; their actual shadings are the separately supplied translated measurable intersections throughout.

The bounded estimate is invoked with fixed separation and fixed base radius before any original family, positions, scale, density, or shading data. It is then applied to every translated group. Summing the actual tube-volume weights counts every original tube once, while the disjoint old group-union bound controls the right-hand side. The final constant is `c/K(n)^d`. No scale or tube-count factor is lost, and no assumption of equal tube volumes is used. Empty families are handled by the same finite sums.

This realizes the bounded-region reduction described at combined PDF Section 1.1 (physical PDF page 2, extracted lines 54–64). Final applications to the six-dimensional first step and the general limiting exponent are separate small wrappers from already proved bounded maximal estimates.

## Verification and frozen files

Both modules clean-compile with zero diagnostics and have current `.olean` files. Exact full-source environment audits include all locally generated declarations and report only `propext`, `Classical.choice`, and `Quot.sound`; no custom axiom or admitted proof is introduced.

| Module | Source theorems | Definitions / structures | Audited local declarations | SHA-256 |
| --- | ---: | ---: | ---: | --- |
| MeasurableUnitPartition | 12 | 5 / 1 | 37 | `eba0ef701d0a714dfc0d46c2a1c2a0786b0d39ae65d2305ed34e27b09220bf2a` |
| MaximalPositionReduction | 10 | 2 / 0 | 19 | `6fc8fce648451195825507e1bb3e00e242cc663b4e07985ba4f22f7fdab30ace` |

Evidence is in `MeasurableUnitPartition_audit.json`, `MaximalPositionReduction_audit.json`, their full-source audit copies and logs. A separate agent re-read both frozen sources and found no defect; see `measurable_position_reduction_independent_review.md`. No frozen prior module or shared registry was edited.
