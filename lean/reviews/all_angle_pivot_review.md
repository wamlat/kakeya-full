# Read-only review of the all-angle pivot assembly

Reviewed the frozen `AllAnglePivot.lean` (SHA-256 `442d13e8f9a331edcc59532bfa61f1028c9eddf9186d2530b88cdb128c8a5cf4`), together with `AngularBoxAllCases`, `AngularSpatialSummation`, the actual population/support statements in `AngularSpatialSampling` and `AngularSpatialBudgets`, and `CoarseBounds`. No mathematical statement or composition defect was found. This is a separate agent's mathematical cross-review; the root's exact-source Lean/axiom audit is a separate check.

The final `all_scales` statement establishes

`c A⁻¹ δ^(m − D + ε) λ^C M ≤ #F.unionCells`,

where `D = pivotSet m d'` and `C = pivotDensity pExp qExp`. Its positive constant is chosen before the family, scale, density, cap constant, and population. The fixed parameters include ambient dimension, all exponents, width, base radius, the full two-ends coefficient `B`, and its exponent `alpha`.

The checked links are:

- **Actual construction and quantifiers.** `logarithmic_range` constructs the angular pieces `P`, every retained refinement `V`, and every spatial package `U` from the original family. The same `U` is supplied to each local case. It does not assume marked broadness, a spatial box decomposition, a sampling outcome, a selected density class, or a desired local count. The zero-tube case is explicitly handled; positive population is used only to construct the pieces.
- **Original support.** The local estimates count `SpatialGridPopulation.refinedCells` in the original grid. Summation uses the proved bound on these same finite sets over all good boxes and all kept angular groups. It does not substitute a count of newly sampled cubes or infer discrete overlap from a volume bound. The exact common-map support in each `Package` is retained through the local high-density argument.
- **Population and logarithms.** The actual population lower bound costs four powers of the original logarithm, and the physical density lower bound costs one. Raising the latter to `C` gives the combined `C+4` logarithmic loss. `cancel_logarithmic_overlap` absorbs precisely this loss with `ε/2`. The other `ε/2` is the local estimate's loss, so the final exponent is exactly `m−D+ε`.
- **Angular powers.** The chosen positive `beta = min(1,m−D)/2` satisfies `beta ≤ m−D+ε/2`. Thus the local angular gain cancels the proved `tau^(−beta)` old-cell overlap in the correct direction. The hypothesis `D < m`, stronger than the local case theorem's `D < m+1`, is explicitly required here; it is not silently inferred.
- **All scales and normalization.** Enlarging the fixed width to `max(width,1)` and base radius to `max(R,1)` preserves the original axes, full shadings, cap bound, separation, comparability, and two ends. The width-power test is proved for every ambient dimension `k+2`. For `δ ≤ 2/exp(1)`, the natural logarithm is at least one. Above that fixed cutoff, `CoarseBounds` uses the actual cap total-count bound and one actual shading; it applies to the same original configuration. The minimum of the fine and coarse constants is fixed before configurations. No scale-dependent normalization constant is introduced.

The remaining scope is explicit. The theorem assumes the two analytic input propositions `DiscreteEstimate (k+2) m d pExp` and `DiscreteEstimate (k+3) d d' qExp`; the claimed recursive step is conditional on exactly those propositions. It also assumes the original full-shading two-ends inequality at every ball radius between `δ` and one, with fixed `B ≥ 1` and `alpha > 0`. It requires unit `δ` projective-direction separation. Consequently this statement alone is not the unrestricted `DiscreteEstimate` for arbitrary normalization, and it does not remove two ends. It requires the stated real-parameter range, including `1 ≤ m`, `m+1 ≤ k+2`, `pExp ≥ 1`, `d ≥ 0`, `qExp ≥ 2`, `D < m`, and the positive sparse-density margin. These conditions are visible rather than hidden in a construction record.

No frozen source was edited in this review.
