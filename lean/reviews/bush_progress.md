# Cumulative bush theorem: complete finite geometric proof

`formalization/Bush.lean` compiles cleanly to `.lake/build/lib/lean/Bush.olean` with 24 theorems and 10 definitions. Audits of `cumulative_bush_square`, `cumulative_bush_lower_bound`, and `bush_real_cap_estimate` list only `propext`, `Classical.choice`, and `Quot.sound`. There is no `sorry`, `admit`, or custom axiom.

## Main result and exact scope

The module proves the discrete cumulative bush estimate in Appendix A.1 of the combined PDF (physical page 36), for actual finite Euclidean tube/grid data:

E ≥ c(d,width,m) A⁻¹ δ^(m/2−1) s^((m+2)/2) M.

Here E is the actual cardinality of `TubeFamily.unionCells`; total actual shade incidence is at least s M/δ; m>0, 0<δ≤1, 0<s≤1, A≥1, and M≥1. Individual shadings may be empty or have unequal sizes. `Admissible` means every actual shading-cell center lies within width*δ of an actual point on the unit tube's axis segment. `CapBound` is the original actual projective-chord cap inequality for all unit cap centers and radii δ≤r≤1. No bush estimate, incidence energy bound, total-tube bound, or geometric packing assertion is assumed as an extra hypothesis.

The theorem `cumulative_bush_estimate` chooses the positive constant before M, the tube family, δ, s, and A. It accepts an arbitrary fixed width by enlarging it to max(width,1). Direction separation and a common bounded ambient region are unnecessary additional hypotheses for this particular argument; the result uses the supplied actual cap condition and unit-tube geometry.

`bush_discrete_estimate` then proves the complete existing `DiscreteEstimate` predicate with d=p=(m+2)/2, including every positive scale-loss parameter ε and its uniform constant. `bush_real_cap_estimate` proves the existing `RealCapEstimate m ((m+2)/2) ((m+2)/2)` predicate for every m>0. This is an actual unconditional analytic seed in that finite model, rather than a theorem whose hypothesis is the desired seed estimate. It does not establish the novel pivot improvement or the combined PDF's final six-dimensional exponent.

## Proof details and constants

Let d=k+1 be the actual ambient dimension. For width W≥1 define

L = (6+4W) [2 ceil(W+1)+3]^d,
D = 64 W L,
P = ProjectiveGeometry.packingConstant(k),
K = 8 D^m + P D^(m+2) + 1,
c = 1/sqrt(K P).

These deliberately generous constants are fully explicit and independent of δ, s, A, M and the individual family. No constants have been optimized.

The proof proceeds through the actual finite incidence relation. It proves the sum of tube shade counts equals the sum of cell degrees, deletes tubes below s/(2δ), and chooses a maximum-degree occupied cell. Actual near and far cells partition each shading exactly. For density s≥Dδ, choose the physical radius r=s/(8L); the previously proved tube-ball count bounds all removed incidences, and every retained tube keeps at least s/(4δ) far cells. `PivotDirections.two_cell_cap_multiplicity` derives and applies an allowed-range cap to every distant cell. Its cap-radius conditions δ≤8Wδ/r≤1 are explicitly verified from this radius and density cutoff. Double counting proves

s^(m+2) M ≤ 8 D^m A δ² E².

For s≤Dδ, `CapCover.cap_bound_total_count_scale` supplies the actual bound M≤P A δ^(−m), and positive actual cumulative mass supplies E≥1. This gives the same square inequality with P D^(m+2) in place of 8 D^m. The combined constant K covers both cases. Taking square roots and using the actual total-count bound a second time gives the displayed linear-in-M result. All real-power identities, positivity conditions and square-root comparisons are proved.

## Dependencies and remaining work

Dependencies are actual Euclidean `Configurations`, proved `GridGeometry`, root's proved `TubeLocalCount`, proved `ProjectiveGeometry`/`CapCover`, and the displacement/cap geometry in `PivotDirections`. Earlier `PivotWitnesses` and `PivotSupport` enter through imports, but the bush argument does not assume their support or energy conclusions.

The theorem is discrete. It does not prove the measurable-shading transfer by itself, the stronger fractional hairbrush seed from Section 4, the collision-shell strip count (5.17), the upper lifted energy estimate, or the final pivot/glob-alization theorem. These remain distinct tasks. The result covers the cumulative bush input actually used in Appendix A.2 without requiring comparable per-tube density.
