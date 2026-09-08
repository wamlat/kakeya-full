# Exact localized lattice transport and estimate equivalence

6 September 2026. These are actual geometric and analytic interfaces, not a proof of the manuscript's unrestricted seed or pivot.

`LocalizedGridTubes.lean` snaps a common coarse cluster origin to the original fine lattice and derives its dimension-only distance from every localization center. The common spatial rescaling then carries fine cell centers to an exactly translated lattice. From an actual nonempty localized finite shading, the proof constructs an axis interval of length 8 max(1,width) rho and a controlled starting point. The resulting actual unit-tube family is admissible and uniformly bounded; each shading cardinality and the entire union cardinality are preserved exactly. The axis interval and normalized base bound are conclusions rather than premises.

`GridTwoEnds.lean` proves the exact bijection between original and rescaled finite center-ball tests. All-radius two-ends transport follows by applying the original local-radius bound when available and total cardinality otherwise. For the actual localized tube dilation, the constant is (32 max(1,width))^alpha, independent of density and the selected scale.

`MeasurableToDiscrete.lean` proves the full uniform converse from MeasurableEstimate to DiscreteEstimate. Each actual grid shading is realized by its half-open cell union and all shadings undergo one common width-normalizing homothety. A fixed geometry-dependent density divisor ensures the actual shading-to-tube-volume requirement. Actual union volume is exactly δ^n/W^n times the original union cell count; this positive factor cancels. The estimate constant is chosen before every configuration, scale, density, cap coefficient and tube count.

Together with the previously proved forward conversion, `discrete_iff_measurable` establishes equivalence of the concrete predicates for positive integer ambient dimension and 1≤d≤p. The converse itself does not require those exponent restrictions. This permits the remaining seed assembly to use exact measurable anisotropic images and return to the original discrete formulation through a proved implication.

No comparison of unrelated image unions or of anisotropic images with enlarged new full grid-cell unions is assumed. No theorem in these modules supplies the missing seed, pivot or maximal-operator estimate.
