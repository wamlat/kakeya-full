# Exact-image two-ends and angular broadness transport

AnisotropicTransport.lean proves the actual affine-image interfaces needed before measurable restoration. The common inverse is the actual box homeomorphism inverse. Pointwise membership and finite incidence sets are equal under this inverse, with no almost-everywhere exception.

For0<tau≤1, the image intersection with a physical ball of radius r is contained in the image of the old shading intersected with the old ball of the same radius centered at the inverse image of the new center. This follows from the proved expansion of every Euclidean distance. Therefore an all-radii old two-ends inequality B*r^alpha transfers with the same B. The new lower test radius delta/tau is at least delta; finite old measure ensures legitimate real-measure monotonicity. The exact tau⁻k volume factor cancels.

For pointwise angular broadness, let C=4(1+2angular)^2 be the actual inverse projective-chart constant. A nonempty transformed cap of radius r is pulled back around an actual occupied member into an old cap of radius2C*tau*r. For r≥delta/tau this radius is≥delta. Original broadness at angular scale tau therefore gives new broadness at angular scale1 with coefficient K*(2C)^beta. The proof handles arbitrary cap centers and uses all-radius Broad, without silently importing a cap condition above radius1. The pointwise local direction condition need only hold for indices whose shading is nonempty, and the finite occupied set is transported exactly.

These are properties of the exact full image references. An arbitrary subsequent subset is not claimed broad or two-ended without proportional recovery. The measurable recovery module supplies that distinct step.

Lean4.33.1, Mathlib commit0df444a360eaa60ab8c11dca51a86af692955474. Module compilation and a full-source seven-theorem axiom audit are recorded as anisotropic_transport_axioms.lean/log in audit_work. Only standard foundation dependencies are admitted; no sorry or custom axioms.
