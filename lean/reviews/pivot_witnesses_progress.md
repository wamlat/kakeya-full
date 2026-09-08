# Legal finite-sample witnesses checkpoint

`formalization/PivotWitnesses.lean` compiles with Lean 4.33.1/mathlib 0df444a360eaa60ab8c11dca51a86af692955474. It contains 17 proved theorems, 13 definitions, and 6 records. The main constructions and theorems report only Lean's standard `propext`, `Classical.choice`, and `Quot.sound` axioms. There is no `sorry`, `admit`, or custom axiom.

## What is now derived

The input angle has two actual Euclidean unit vectors with transverse separation at least κ. Its common intermediate coordinate is at least κ. Each endpoint pair has first coordinate b≤1, gap b−a≥κ, and κ≤|c|≤1; the sign of c is unrestricted. These are normalized legal-sample conditions from (5.11).

The exact pivot z=x+a u₁+c(1−a/b)u₂ is proved to lie on the actual endpoint segment. Its coefficient has magnitude at least κ², its separation from the first endpoint is at least κ³, and the endpoints have distance at most 2. Two actual samples in one common angle/intermediate/pivot-cell fiber have coefficients differing by at most 2Cδ, because their exact pivots are both close to the same grid center. No scalar perturbation assumption is added.

Choosing an actual reference pair in this fiber fixes its nonzero graph-line coefficient u₀. The lift parameter t=c/u₀ is proved to satisfy 1+κ/2≤t≤2/κ at 2Cδ≤κ⁵/4. Its affine residual is proved to be at most 8Cδ/κ². The segment, separation, lift range, and residual are then used to construct the earlier `PivotSupport.RoundedLiftWitness`.

The module also defines actual coordinatewise floor rounding, with Euclidean error ≤kδ, and actual lifted-point rounding with horizontal error ≤kδ and vertical error ≤δ. `Fiber.rounded`, `ShadedPair.attachRounded`, and `RoundedSampleInput.attach` derive all reference-pivot, intermediate, target-pivot, and lift-rounding bounds. Here C≥k+1. The only closeness assumptions remaining in `RoundedSampleInput` concern original occupied endpoint labels and their chosen exact axis projections. Equality of two floor-rounded pivot labels is the actual finite-output fiber relation.

## Finite energy statement

For any finite set of such samples with endpoint labels in an actual occupied-cell set E, `rounded_sample_support_count` proves

|support| ≤ |E|² · pivotCount(k,δ,4C,2+2C) · liftCount(k,δ,2Cδ,8Cδ/κ²,κ³,2/κ).

The preceding `PivotSupport` theorems give the first factor after |E|² as O_C,k(δ⁻¹) and the second as O_C,k(κ⁻⁵), with explicit constants. Thus this recovers the geometric support bound behind (5.31), allowing its weaker κ⁻⁶ statement as well. The scale assumption is implied by the manuscript's stronger sufficiently-small δ relative to κ²⁰, after absorbing fixed constants.

`incidenceWeight` is defined as the actual cardinality of each finite label fiber, and its sum is proved equal to the sample count. `rounded_sample_energy` consequently proves the lower-energy inequality with the square of actual sample count on the left. We do not assume a support bound, a mass identity, an exact-segment condition, or a residual bound in that final theorem.

## Limits and next dependencies

The module is an actual finite legal-sample construction and geometric energy theorem. It does not yet construct the abundant legal samples from an admissible shading family, prove their λ³N³ abundance, implement the selection of equal-size fibers across angles, identify its discrete energy with the manuscript's chosen lifted shading energy, or prove the upper energy estimate. Its fixed C, unit-axis and normalized-length conventions are a concrete version of the manuscript's implicit geometric constants; applying it to a general shading still requires the corresponding normalization and selected axis projections.

The angle record fixes the intermediate point within each fiber, as required by (5.12). `AttachedSample` is a more general intermediate interface that permits arbitrary geometrically close lift cells; `RoundedSampleInput` is the stronger concrete constructor that chooses a deterministic rounded exact lift. This distinction is intentional and explicit.
