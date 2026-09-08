# ProjectiveGeometry: actual projective cap packing with dimension-minus-one exponent

## Completed result

`audit_work/formalization/ProjectiveGeometry.lean` contains 42 theorem declarations and compiles cleanly. It imports the actual Euclidean definitions from `Configurations.lean` and the proved integer-box count from `GridGeometry.lean`.

For ambient dimension d=k+1, the module proves an explicit full projective cap packing estimate:

**If finitely many actual unit vectors are separated by projective chord distance at least delta>0 and belong to a projective chord cap of radius r≥delta, then their number is at most**

`C_d * (r/delta)^(d-1)`, where `C_d = 2*d*[4*d*(d+1)+5]^(d-1)`.

The result also holds for indexed families and counts their original indices. No packing, proper-coloring, bounded-cover, or direction-map injectivity conclusion is assumed. In particular the exponent is **ambient dimension minus one**, not ambient dimension.

## Proof construction and genuine geometric content

1. The actual `min(norm(v-w), norm(v+w))` satisfies symmetry, antipodal invariance, triangle inequality, and zero distance precisely when v=w or v=−w. It is treated as a pseudometric on representatives; antipodal vectors are intentionally identified.
2. Euclidean l2 norm is bounded by the sum of coordinate absolute values. Every unit vector in dimension d therefore has some coordinate of absolute value at least1/d.
3. On a unit-sphere chart where the zeroth coordinate is at least c>0, all remaining k coordinate differences bounded by h imply full Euclidean distance at most `(k+1)*(1+1/c)*h`. The proof uses the unit-sphere quadratic identity to recover the missing coordinate, not a dimension-k+1 ball count.
4. Quantize only those k remaining coordinates with mesh `delta/[2*(k+1)*(1+1/c)]`. The inverse chart bound proves that a bin cannot contain two projectively delta-separated vectors. The integer labels of vectors in a radius-r cap belong to an explicitly counted k-dimensional box. This gives the dimension-minus-one exponent.
5. Coordinate permutations and sign changes are explicitly proved to preserve norms, ordinary distances and projective distances. The largest-coordinate argument covers the sphere by2d signed charts. Summing their established chart bounds yields the full spherical estimate.
6. An explicit sign choice maps each projective-cap representative into the ordinary Euclidean radius-r ball about the cap center. Positive separation proves this map is injective on the original finite family, so no original elements or multiplicities are lost.
7. The indexed theorem separately proves injectivity of the original direction map from the separation hypothesis; it does not replace tube count by the number of distinct directions without justification.

## Connection to the existing tube definitions

`separated_tube_family_cap_bound` proves the actual predicate

`F.CapBound delta (k:Real) (fullDirectionCoefficient k separation)`

for `F : TubeFamily (k+1) M`, delta>0, separation>0, and `F.Separated (separation*delta)`.

Here `fullDirectionCoefficient k separation = C_(k+1) * [1/min(separation,1)]^k`, and its value is proved at least1. The cap coefficient is independent of delta, radius, tube count, positions and directions. The use of the minimum accommodates every positive fixed separation normalization, including values above1, without an extra restriction on cap radii.

`separated_total_tube_count` gives `M ≤ C_(k+1)*(1/delta)^k` for unit-direction families separated at delta≤1. It directly uses the sphere's distance1 from the center zero. This is a full-dimensional packing consequence and should not be confused with deriving a fractional-m total count from a fractional cap bound.

## Angle comparison

The module proves the exact unit-vector identity

`projectiveDistance(v,w)^2 = 2 - 2*abs(inner(v,w))`.

For Mathlib's actual angle between v,w, the squared sine is between half the projective chord squared and the whole projective chord squared. Sine is unchanged by the antipodal choice. The maximal projective chord distance is also proved at most sqrt2.

A separate formal definition of the unoriented angle as the minimum of theta and pi−theta, and inequalities comparing that angle itself linearly with its sine, are not included. The existing squared-sine comparison is the precise completed angular interface; a full angle/chart convention equivalence should not be claimed merely from the comments.

## Scope still open

- Fractional real-cap preserving geometric thinning requires the actual dyadic-chart hierarchy and scale-dependent integer capacities to be constructed, then linked to the finite selection module. This module proves full-dimensional packing, not that fractional selection construction.
- Packing in strips near a prescribed two-dimensional plane, or the sharper collision-shell bounds required by the pivot, needs additional subspace geometry. An ordinary spherical cap bound alone does not establish such strip estimates.
- The pivot, collision, lifted-energy, sampling, localization and measurable maximal arguments are not consequences asserted by this file. The new results provide concrete geometric inputs for those modules.

## Main usable interfaces

Namespace: `KakeyaFormal.ProjectiveGeometry`.

- `projective_triangle`, `projective_symm`, `projective_zero_iff`.
- `spherical_chart_packing`, `spherical_chart_packing_real`.
- `spherical_cap_packing` (ordinary Euclidean cap, still projective separation).
- `projective_cap_packing` (actual projective cap).
- `indexed_projective_cap_packing` (original index cardinality).
- `packingConstant_formula`, `packingConstant_ge_one`.
- `separated_tube_family_cap_bound`, `fullDirectionCoefficient_ge_one`.
- `separated_total_tube_count`.
- `projective_chord_sq`, `projective_angle_sine_sq`, `projective_distance_le_sqrt_two`.

The packing theorems are parameterized by k while their vectors live in `Space(k+1)`; their exponent k is therefore the ambient dimension minus one. The center in the packing theorem need not itself be a unit vector, while the existing tube cap predicate restricts its center to unit vectors.

## Verification

From `audit_work/formalization`:

```sh
/Users/ssoh/.elan/bin/lake env lean -o .lake/build/lib/lean/ProjectiveGeometry.olean ProjectiveGeometry.lean
```

Final compile: exit0, no warnings or errors. Lean4.33.1, Mathlib commit `0df444a360eaa60ab8c11dca51a86af692955474`. No `sorry`, `admit`, `native_decide` or custom axioms are used. The full-source dependency audit is in `audit_work/projective_geometry_axioms.lean`, and its output is recorded in `audit_work/projective_geometry_axioms.log`.

The completed dependency audit reports all 42 theorem declarations using only `propext`, `Classical.choice`, and `Quot.sound`; no `sorryAx` or custom axioms occur.
