# Actual finite measurable energy

`MeasurableEnergy.lean` proves Cauchy–Schwarz in the actual L2 space and then derives the finite shading identity and union bound. The functions are the genuine finite sums of set indicators. Measurability, L2 membership, integrability, exact integral of the multiplicity and exact pair-intersection energy are all proved from the finite measurable shadings and their finite measures.

Main conclusions:

- `(sum_i measure(Y_i))² ≤ measure(union_i Y_i) * sum_ij measure(Y_i intersect Y_j)`.
- Actual pairwise majorants may be substituted.
- If every shading has mass at least λ≥0 and every actual row of pair intersections has energy at most B>0, the union measure is at least `M*λ²/B`. The empty family is included.
- For actual Euclidean unit tubes, shadings contained in their δ carriers have pair-energy majorants `44*2^k*V_k*δ^k/max(projectiveDistance,δ)`, by the separately proved TubeIntersection theorem.
- An actual pointwise multiplicity bound K gives `sum_i measure(Y_i) ≤ K*measure(union_i Y_i)`, proving the finite measurable bounded-overlap assembly used by plane bins.

The tube conclusions do not assume an intersection-volume estimate. The generic row-energy specialization states its row bound explicitly; the angular shell summation supplying the hairbrush row bound is a separate remaining lemma. Neither this module nor TubeIntersection asserts the full hairbrush or Kakeya theorem.

Individual source compilation passes with no warnings. The next package-wide isolated build and all-local-theorem axiom inventory will certify the delivered checkpoint.
