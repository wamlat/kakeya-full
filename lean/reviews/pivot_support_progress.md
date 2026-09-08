# PivotSupport checkpoint

6 September 2026. Module: `audit_work/formalization/PivotSupport.lean`.

## Validation

Fourteen theorem statements compile successfully under the development Lean 4.33.1/mathlib project. The final run exited zero with no warnings. Printed axiom checks for the fixed-triple count, legal-witness support count, legal-witness grouped energy, normalized lift count, and pivot scale bound contain only `propext`, `Classical.choice`, and `Quot.sound`. No `sorry`, `admit`, custom axiom, or unsafe declaration is used.

The module imports the compiled `TubeGeometry`, `GridGeometry`, and `Finite` modules. It builds on the actual scaled integer grid from `Configurations`. A lift cell is represented as `(horizontal integer cell, final integer coordinate)`, i.e. an explicit product integer grid. No finite type for the entire infinite lattice is asserted.

## What is now proved

1. A finite set of integer vertical coordinates in a real-centered interval of radius `R` has at most `2 ceil(R)+3` elements.
2. Horizontal Euclidean-ball localization and vertical interval localization give an actual product-grid count with a dimension-dependent horizontal factor and a *linear* vertical factor.
3. A `RoundedLiftWitness` carries exact endpoint/pivot representatives, actual segment membership, their distances from the original grid centers, a quantitative exact separation, the lift parameter and residual, and horizontal/vertical lift-cell errors. Different incidences may have different exact representatives while sharing the same rounded labels.
4. For one fixed endpoint/pivot triple, `fixed_triple_lift_count` derives its lifted-grid support cardinality from these geometric witnesses using the proved parameter-recovery theorem. It assumes neither a support-cardinality bound nor a parameter-interval bound.
5. `rounded_segment_proximity` proves that an exact pivot on the segment between exact endpoints lies within `2 err` of the segment between the rounded endpoints.
6. `endpoint_triple_count` derives the number of triples from the actual segment-grid count, including degenerate endpoint segments. Its dependence is quadratic in the original occupied endpoint count and linear in the number of mesh subdivisions along the bounded segment.
7. `support_count_by_triples` and `endpoint_lift_support_count` combine the two geometric counts through the already verified finite fiber-counting theorem.
8. The stronger `support_count_from_legal_witnesses` derives the set of triples and their rounded segment-proximity condition internally from the actual witnesses. Only original occupied endpoint membership and a fixed endpoint-length bound remain as external geometric normalizations.
9. `finite_image_support_energy` handles the infinite ambient integer lattice by summing only over its finite image of actually occupied energy positions. It is the finite-image version of the previous support-sensitive Cauchy–Schwarz argument.
10. `energy_bound_from_legal_witnesses` supplies the actual grouped lower-energy inequality. Its groups are `(pivot grid label, lifted grid cell)`. The integer unit-slab label is determined by the lifted final coordinate, so it does not introduce an independent extra factor. The support cardinality is established inside the proof, not assumed.

## Exact cardinality and energy form

Write

- `P = (ceil(D/delta)+1) * (2 ceil(width+1)+3)^k`;
- `V = (err + 4*(residual+(2*timeBound+2)*err)/separation)/delta`;
- `H = (2 ceil(2 err/delta)+3)^k * (2 ceil(V)+3)`.

The proved support bound is

`#support <= (#occupied)^2 * P * H`.

For nonnegative incidence multiplicities on occupied `(triple,lift-cell)` labels, the proved energy inequality is

`(total incidence mass)^2 <= (#occupied)^2 * P * H * grouped_energy`.

This has the exact structural content required before (5.32). The strong legal-witness version uses `width=2 err/delta`, deriving that width from endpoint rounding.

## Kappa dependence and comparison to the manuscript

The final two metric-scale substitutions are also formally proved:

- For `err=C delta`, `residual=4C delta/kappa^2`, `separation=kappa^3`, `timeBound=2/kappa`, `C>=1` and `0<kappa<=1`, the normalized vertical radius is at most `41 C/kappa^5`.
- The actual lift-position bound is therefore at most

  `87 C * (2 ceil(2C)+3)^k / kappa^5`.

- For `delta<=1` and bounded endpoint length `D>=0`, the pivot-grid factor is at most

  `((D+2)/delta) * (2 ceil(width+1)+3)^k`.

Thus the formalized pieces preserve the expected `delta^(-1) kappa^(-5)` support dependence with fixed dimension/rounding constants. The manuscript weakens this to `kappa^(-6)`; no worse kappa power is forced by these grid counts, and no ambient-dimensional power `kappa^(-5k)` was introduced. In particular this phase does not force a change to the stated six-dimensional conditioning exponent 58. The exact multiplication of these separately proved factors is elementary; the package does not yet include the entire original theorem with those constants substituted.

## Still required for the full theorem

The module proves the grid support and energy consequences of actual geometric lift witnesses. It does not yet construct one such witness for every selected discrete angle-output fiber, count/trim those fibers with all marked-mass identities, or prove the collision shell count. The exact pivot/lift metric ingredients needed to construct these witnesses are in `TubeGeometry`; connecting the actual finite sample data and rounded grid-cell assignment to the witness structure is the next natural interface.

Random projection, concentration/sampling, analytic Wolff inputs, real-cap packing, localization choices, full measurable shadings, and maximal-operator interpolation remain separate dependencies. This checkpoint is not a formal proof of the unrestricted maximal theorem.

Compile command:

```
/Users/ssoh/.elan/bin/lake env lean PivotSupport.lean
```
