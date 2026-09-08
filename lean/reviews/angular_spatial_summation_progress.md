# Original-cell angular/spatial summation

AngularSpatialSummation.lean compiles cleanly and passes the complete local-declaration audit: two source theorems, 9 audited local declarations, all standard-foundation only. Source SHA256 6cbd10d28d2ba103973bd734b0863260555edab2d72f9871dca0d547e1d88d7a.

The scalar theorem cancel_logarithmic_overlap cancels precisely the actual overlap factor K*tau^(-beta), using beta<=s and delta^s<=tau^beta*(delta/tau)^s. The physical density lower bound costs L^(-C), and total retained population costs L^(-4); their combined loss L^(-(C+4)) is absorbed into an arbitrary positive additional scale loss. The constant is fixed before both scales, density, cap coefficient, population and counts.

from_piece_estimates is an actual-family summation theorem. It takes the original angular Pieces, every actual refined reference and its constructed SpatialData, together with a uniform per-box old-cell estimate. Density lower bounds, population retention and old-cell overlap are all obtained internally from AngularRefinementBudgets, AngularSpatialBudgets.total_population and AngularSpatialSampling.total_old_count. The sums run over the same original kept groups and all literal good boxes. It assumes no sampled-cube overlap, equality of old/new volume normalizations, or desired whole-union bound.

The explicit analytic interface is the per-box estimate. AllAnglePivot separately constructs every Pieces/Refinement/Package and discharges that interface using AngularBoxAllCases. The summation lemma alone is not claimed as an unrestricted pivot. Independent review is in angular_spatial_summation_review.md.
