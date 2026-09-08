# Actual measurable sampling means

`SamplingMeans.lean` connects the actual measurable inputs of source Lemma 6.1 to the finite coupled sampling law. The development uses the original finite tube indices and the exact finite positive-cell support constructed in `SamplingSupport`; it does not assume a cell cover, a probability mean estimate, or a new incidence geometry.

## Exact mass and probabilities

The `weights` map is literally `weight (Y i) delta z.val` on the subtype of the chosen finite grid support. `cell_mass_sum` and `weight_sum` prove the finite disjoint-half-open-cell measure identities. `candidates_cover` derives a finite cover from the original bounded carriers. `support_mass` then proves that removing every zero full intersection loses no full or marked mass: any positive marked contribution would, by measure monotonicity, also be a positive full contribution already included in the support.

`fullMean_eq` gives exactly `fullMean_i = volume.real(Y_i)/delta^n` for full or marked subsets Y_i of the original full family. `marked_total_mean` gives the exact total expected marked mass `sum_i volume.real(G_i)/delta^n`. These are identities on the actual finite probability index type, not formal infinite sums.

For ambient n+1, `fullMean_density` converts the actual per-tube mass interval `[c0 lambda delta^n, C0 lambda delta^n]` into `[c0 lambda/delta, C0 lambda/delta]` for the original expected full count. Together with the previously proved coupled-weight inequalities, this supplies the concrete meaning of source (6.5) and the full-density means used in (6.14).

## Ball expectation geometry

A cell whose center lies in B(x,r) is wholly contained in the closed ball of radius `r+n delta/2`, using the actual grid-cell distance theorem. `ball_weight_le` combines this geometric inclusion with the exact cell mass identity; it bounds the actual weighted ball-mask sum by the normalized full mass in that enlarged physical ball.

For every r≥delta, `ball_weight_two_ends` proves

`sum_(center in B(x,r)) weight(Y,delta,z) <= B (1+n/2)^alpha r^alpha volume.real(Y)/delta^n`.

Only the original full two-ends tests at radii delta≤t≤1 are assumed. If the enlarged comparison radius `(1+n/2)r` is above one, the proof uses total mass and `B[(1+n/2)r]^alpha≥1`. It does not apply two ends outside its stated range or below delta. The hypotheses are B≥1 and alpha≥0. For the manuscript's alpha≤1, the dimension/alpha factor can additionally be bounded by 1+n/2 if needed; the theorem keeps its exact value visible.

`ballMean_eq` identifies the probability module's Boolean ball mask with `SamplingBallTests.testCells`. `ballMean_two_ends` applies the geometric estimate to all the actual support-centered dyadic tests and rewrites the normalized total mass as their exact original fullMean. Carrier geometry supplies finiteness in this input-facing wrapper. This discharges the geometric expectation part of (6.15), including the enlarged-radius fallback. Choosing a cutoff at least four times the proved upper bound is still an explicit scalar step in the simultaneous assembly.

## Angular expectation geometry

`cell_incidence_mass_le` integrates a genuine almost-everywhere finite incidence-count inequality over one actual cell. Its integrability and all finite sum/integral interchanges are proved from measurable markings and the cell's finite volume. It requires no assumed bound on the integral. `cell_incidence_weight_le` divides that proved result by the exact positive cell volume.

`cap_mean_le` specializes this to the actual original-direction open tests

`projectiveDistance(direction_a,direction_i) < 2 theta`.

It accepts a pointwise inequality at just that tested radius. `cap_mean_from_broad` obtains it from the existing formal Broad predicate. `cap_mean_from_bounded_radii` instead uses an almost-everywhere cap hypothesis only at physical/angular radii delta≤r≤1, with unit cap centers, and requires explicitly delta≤2theta≤1. Thus no extra all-radius broadness hypothesis is needed. The open tested cap is a subset of the closed cap counted in this source-compatible formulation.

Finally `capMean_admissible` discharges the exact probability input

`1000 capMean <= markedMean`

from those geometric hypotheses and the scalar condition `1000 K (2theta)^beta≤1`. This uses the exact `SamplingCapTests.cap` Boolean mask, not a separate hypothetical direction net.

## Scope and remaining assembly

The module proves the actual mass and expectation interfaces in (6.5), (6.15) and (6.17). The finite probability/Chernoff construction is already separate and proved. The geometric ball and cap test families, support counts, and asymptotic failure-budget estimates are owned by their respective separate modules. This file does not claim the full count-or-discretize Lemma 6.1 or the angular globalization proposition by itself. Their remaining application must combine these interfaces on one actual support and preserve original union support and marks in the chosen outcome.

## Verification

The module contains 20 theorems and one definition. The module is clean-built and frozen. Its fresh full-source audit passed with an exact source-prefix match, all 21 named declarations, no errors or warnings, and axiom union exactly `propext`, `Classical.choice`, `Quot.sound`. No sorry or custom axioms have been introduced.

Source SHA-256: `76834dd89f7d6d1abe528ecdfe4d96521fdc3cfc4e5ccdf475128a10876775c4`.
