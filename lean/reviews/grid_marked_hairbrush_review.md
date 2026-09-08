# Independent review: GridMarked and GridHairbrush

Reviewed the definitions and complete proof statements of both modules without editing them. No mathematical flaw or hidden geometric conclusion was found.

`GridMarked.marked_inter` identifies actual intersection with the common normalized marked cell set exactly, using the unique half-open cell label at the inverse image point. The marked and full incidence masses therefore have precisely the same factor `δ^n/W^n`. `marked_half` transfers the finite half-incidence inequality without requiring per-tube marked mass. This is the correct interface for DensityBroadnessRecovery.

Both broadness interfaces assume broadness only on cells belonging to the marked set. `pointwise_broad` evaluates the finite hypothesis at the actual inverse label of each marked physical point. Its constant is exactly `K tau^(-beta)`. `broad_near_count` correctly includes the strict stem cap in the closed finite cap, using projective symmetry, and does not assert broadness on unmarked points.

`GridHairbrush.realized_density` correctly converts `lam ≤ δ #shade ≤ upper` to measurable density parameters `lam/W^n` and `upper/W^n`, with physical tube scale still δ. The entire family and marked set use one common homothety; the original unit segment becomes a shorter segment and is contained in an extended actual unit tube. Directions and their separation/cap counts are unchanged.

The two-ends constant is exactly `B (1+n/2)^alpha W^alpha`. The first factor accounts for the half-open cell radius, and the second for the common homothety. The above-unit-radius branch is supplied by GridShadingMeasure, so the normalization does not call an unavailable finite two-ends test. Its requirements `B≥1` and `alpha>0` are explicit.

In `finite_broad_hairbrush`, the common `δ^n/W^n` mass factor cancels between marked mass and union measure. The remaining density factors are `lam/W^n` to the power 3/2 and `sqrt(A·upper/W^n)` in the denominator, exactly as displayed. No W-factor is silently discarded. The chosen-radius geometric kernel is genuinely applied; neither a measurable realization nor a hairbrush inequality is an input assumption.

Scope: this is the actual finite marked broad hairbrush inequality for the stated hypotheses, including δ-separated directions, cap exponent m≥1, positive alpha/beta, nonempty tube index, and normalized lam≤1. Density recovery can supply its full-density, marked-half, marked-broadness, and two-ends hypotheses after explicitly adjusting constants by eta. The final global induction/output selection is not asserted by these modules.
