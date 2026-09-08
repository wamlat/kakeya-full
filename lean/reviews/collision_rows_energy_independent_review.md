# Independent review: actual collision rows and energy

Reviewed `CollisionRows.lean` and `CollisionEnergy.lean` against combined PDF (5.17)–(5.18), with their concrete dependencies `CollisionPlane`, `CollisionIntersection`, `ActualPivotFiberCount`, `PlanarEnergy`, and the actual `SampleSystem`/angle/output definitions. No shared source was edited.

**Result: no cardinality, multiplicity, exponent, hidden geometric premise, or circularity flaw found in the inspected statements and proofs.**

## Exact objects and multiplicity

`row S ... a` is the finite set of actual pairs `(competingAngle, sharedOutput)`, where the output belongs to both angles and their original second-tube indices agree. It contains no sample representative or existential witness as a counted coordinate. An output supported by several original sample triples is still one row element per competing angle.

`row_intermediate` derives that the original output's second component is an occupied intermediate label on both first tubes. `row_first_index` embeds every row element's first-tube index into `CollisionPlane.firstIndices`, which is formed from the existence of **any shared output** with the fixed angle. Thus the direction population is aggregated over the entire row, and is not incorrectly multiplied by the output population.

For a fixed competing first tube, `fixed_first_product_bound` is a literal subset inclusion into `(actual marked angles on the fixed tube pair) × (actual shared outputs with intermediate in the first-tube intersection)`. No arbitrary representative map is used or presumed injective. Each counted marked angle is uniquely determined by its vertex and the two fixed tube indices. The actual intersection and per-intermediate pivot-label bounds are applied separately, at the correct levels.

`energy_le_sum_rows` bounds the number of ordered collisions by an injective encoding `(firstEdge, secondEdge) -> (firstAngle, secondEdge)`. Equality of outputs recovers the missing output of the first edge; together with its retained first angle, this recovers that entire edge. This remains valid for diagonal collisions. The exact `collision_energy_count` identity relates this ordered collision count to the actual squared output degrees.

The same-second-tube premise is only imposed for two retained edges sharing an output. This is precisely what the previously proved most-frequent-label selection supplies. It does not incorrectly require one second tube for the whole edge set.

## Bounds and exponents

In ambient dimension `n`, the fixed-first row bound is

`fixedFirstConstant(n,width) / (kappa delta) / max(directionDistance,delta)`.

Its three factors are the actual common-intermediate count `C/max(distance,delta)`, actual pivot count `4 box(n,n/2)(1+2width)/delta` for each intermediate, and actual marked-vertex count `C/(2 kappa)` for the fixed competing-first/fixed-second pair. Their product agrees exactly with `fixedFirstConstant = 2 box(n,n/2)(1+2width) C^2`.

The maximum in the denominator correctly includes the identical-first-tube case and every below-mesh angular shell. The `delta` branch uses a genuine one-tube cell count and does not divide by zero angle. The dyadic inverse-angle sum explicitly starts with `distance <= delta`, then covers every unit projective chord through its finite terminal depth. The terminal bound includes `logb 2 (2/delta)+2`.

`CollisionEnergy` writes the ambient dimension as `n = k+2`. The thin-circle packing contributes `kappa^(-k)`, and the vertex intersection contributes a further `kappa^(-1)`. Consequently the final `kappa^(-(k+1)) delta^(-2)` is exactly `kappa^(-(n-1)) N^2`, matching (5.18), with one logarithm and the total original angle count. There is no extra factor in the number of outputs, samples per fiber, or retained edges.

## Scope and assumptions

The final theorem assumes actual original admissibility, actual projective delta separation, `0<delta<=1`, `0<kappa<=1`, nonnegative physical width, the explicit thin-strip small-scale condition `(6 width/kappa) delta <= 1/2`, and a `SampleSystem` of actual legal original triples. It does not assume collision counts, great-circle packing, per-intermediate output counts, intersection-cell counts, or the desired row estimate. Those are derived through the imported geometric lemmas.

The theorem accepts the actual legal sample system as input. Its abundance is supplied separately by `LegalAngleSamples.construct`; this is an interface scope distinction, not circularity. The collision estimate itself uses legal memberships and coordinate gaps, not a presumed collision/energy conclusion. Empty retained edge sets and absent first-index fibers are covered by the finite formulas.

The physical-to-normalized sample homothety contributes the fixed factor `1+2width` in the per-intermediate pivot count; no hidden inverse-kappa factor enters there. The separation requirement is on the original family, which supplies the unique-direction packing needed by the argument.

## Verification

A separate read-only import audit, `CollisionIndependentAudit.lean`, loads the compiled module and prints axioms for `fixed_first_count`, `row_count`, `energy_le_sum_rows`, and `collision_energy_bound`. All report only `propext`, `Classical.choice`, and `Quot.sound`. The audit compilation log is `audit_work/collision_independent_audit_compile.log`.

This review validates the stated collision theorem and its mathematical scope. It does not claim that the global selected-fiber, normalized group-incidence, or final pivot theorem assembly is complete.
