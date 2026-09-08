# Common-density localization and shared spatial rescaling

`CommonDensityLocalization.lean` compiles 3 theorems; `MeasurableRescaling.lean` compiles 16. Both produce `.olean` files. They contain no `sorry` or custom axiom, and their theorem audits use only Lean standard logical axioms. Logs are `common_density_localization_compile.log` and `measurable_rescaling_compile.log`.

## Constructed common density class

Starting from a finite nonempty family of measurable finite-volume shadings with common positive mass lower bound `base`, upper bound `upper`, and the explicit unit-ball-cover hypothesis of FamilyLocalization, `exists_selection` constructs a common radius and common dyadic localized-mass class. The actual surviving cardinality is at least

`M / ((Jradius+1)*(Jdensity+1))`.

Every retained shading keeps at least rho^alpha of its original mass, belongs to one common mass interval `[b,2b)`, is measurable, and satisfies the previously proved two-ends bounds at every δ≤r≤rho. The second depth obeys

`Jdensity+1 ≤ log(upper/base)/log 2 + alpha*log(1/δ)/log 2 + 2`.

Thus the second class selection has an explicit logarithmic depth; it is not an assumed common-density family.

## Actual shared-origin geometry

For every nonempty shading inside a physical δ-tube and a radius-rho ball with δ≤rho, the module constructs an axis-parameter interval of length 8rho containing all its physical incidences. The new axis base is within 6rho of the localization center. No interval or bounded-base certificate is assumed.

The affine map x↦(x-origin)/(8rho) has an explicit continuous inverse. It takes the shading into an actual unit tube of thickness δ/(8rho). If all localization centers are within Rrho of one common origin, all new tube bases are bounded by `(R+6)/8`.

Measurability, finite measure, and exact Lebesgue scaling are proved for the actual affine images. One **common origin** gives the exact union equality and

`volume(rescaled union) = volume(original union)/(8rho)^k`.

All two-ends ball tests are transported to the new scale, and the full normalized radius range δ/(8rho)≤r≤1 has constant 32^alpha. `shared_origin_family` assembles these facts simultaneously for a finite family.

`localized_volume_upper` combines the constructed rescaled physical tube with TubeVolume to derive the geometric localized-mass upper bound `C(k)*rho*δ^k/δ`. This supplies the previously missing density upper bound proportional to rho.

## Remaining global assembly boundary

The common-density selection accepts the explicit original unit-ball cover from FamilyLocalization. The shared-origin theorem explicitly assumes the localization centers lie in one spatial cluster. The global spatial-bin selection and bounded-overlap sum over clusters are still separate; independently translating each tube's localized shading is not asserted to preserve union volume. Coarse-direction thinning and its later normalized family assembly also remain separate from this spatial theorem.
