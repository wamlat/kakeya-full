# Independent review: configuration quantifiers, endpoint passage and error absorption

Reviewed `Configurations.lean`, `Endpoint.lean`, `LogLoss.lean`, and `ErrorAbsorption.lean` in the development formalization directory on 2026-09-06. Also checked the exact imported `Reduction.finite_depth_transfer` statement. This was a statement/quantifier/domain audit, separate from kernel compilation.

## Overall finding

No incorrect quantifier order, density-power reversal, invalid scale endpoint, cap-coefficient loss, or circular endpoint proof was found. The endpoint results are correctly conditional on the full seed and pivot implications. The four files **do not prove those analytic inputs** and currently concern normalized comparable finite integer-grid shadings, not yet arbitrary measurable shadings.

## Quantifiers and uniformity

`DiscreteEstimate` fixes ambient dimension k and exponents m,d,p first. It then quantifies over fixed geometric normalizations and epsilon>0, chooses c>0, and only then quantifies over the entire configuration, including delta, lambda, A, M, positions and directions. Thus c is uniform in exactly the variables that may vary with scale. It may depend on dimension, exponents, width, separation, bounding radius and epsilon, as intended.

`RealCapEstimate` quantifies over each adequate integer dimension separately, so the constants may depend on that dimension. It does not assert unwanted uniformity as m decreases to3, nor across unbounded ambient dimensions.

`DiscreteEstimate.of_limit` chooses a finite stage before the configuration. The only needed exponent condition is D−d[j]≤epsilon/2; an upper bound d[j]≤D is unnecessary. The code correctly does not assume monotonic convergence. Density powers are bounded above by P, and for 0<lambda≤1 increasing the exponent weakens the bound. The resulting constant can depend on the finite stage and therefore epsilon, but not on lambda, A or M.

The seed and pivot hypotheses of `real_cap_endpoint_from_seed_and_pivot` and `conditional_diagonal_endpoint` explicitly quantify over the required real cap parameters and domains. The final diagonal invocation uses n≥6, m=n−1, and the proven strict limit-profile inequality above4. No dimension-five diagonal result is inferred.

## Integer shading and small density

`Comparable` imposes lambda/delta ≤ card(shade) ≤ 2*lambda/delta on every tube. Together with lambda>0, this makes every shade nonempty whenever M>0. The argument proving lambda≥delta/2 is valid: pick an existing tube, use its positive integer cardinality to get card≥1, and apply the upper comparable-density bound. M=0 is handled separately in `remove_errors`, so no nonexistent tube is selected.

This lower density bound is valid for these comparable integer-grid configurations. It would be invalid for arbitrary measurable shadings. The comment in `ErrorAbsorption.lean` correctly states that boundary. It is also not a bound on an arbitrary smaller density parameter that one may originally attach to the same nonempty shading; it is a bound on the normalized comparable parameter represented in the structure.

`PerturbedDiscreteEstimate` chooses its logarithmic exponent P and constant c after the requested eta and normalization, but before the configuration. This uniformity is sufficient. The proof chooses eta=epsilon/3: one eta is the input scale loss, one pays for the additional density power using lambda≥delta/2, and one pays for the logarithm. The scale accounting is correct. Delta=1 is allowed and causes no logarithmic singularity because log(2/delta)=log2>0.

## Cap and geometric normalization

Cap bounds are imposed for actual unit vectors and projective chord radius delta≤r≤1, with coefficient A≥1 and exact factor (r/delta)^m. The estimate carries one A inverse, and neither endpoint passage nor error absorption introduces a second loss or requires A bounded independently of delta. Separation is a fixed positive normalization constant times delta; constants may depend on that fixed separation constant.

The bounding condition controls tube basepoints rather than every point of the unit segment. Since directions have norm1 and segment parameters lie in [0,1], all axis points lie in the radius+1 region; the grid width adds a fixed further enlargement. This is a reasonable bounded-region convention.

The projective chord distance has maximum sqrt2 on the unit sphere, so radius-one caps do not individually cover the entire projective sphere. That is not a flaw in the definition. Any later derivation of total tube count from the cap bound must provide a finite covering by radius-one caps. Likewise, conversion to the PDF's angular/projective-chart cap convention still requires a geometric comparison and fixed covering argument. The current files do not silently claim those facts.

## Remaining interfaces / caution about claiming equivalence

1. The exact factor-two comparable-density normalization with lambda≤1 is a restricted class of raw finite shadings. Arbitrary counts, densities above the chosen normalization, and empty shadings require the planned normalization/cumulative-density arguments before this predicate can be identified with every formulation of K in the PDF.
2. `DiagonalDiscreteEstimate` is a definition for finite discrete configurations. It is not yet the measurable shaded-union assertion M_n(a) or the maximal-operator norm bound. Their conversion requires the occupancy, localization and analytic arguments under construction.
3. The structure allows k=0 or very low ambient dimensions, but a nonempty unit-tube configuration in dimension0 cannot exist; empty families satisfy the estimate trivially. This harmless low-dimensional vacuity is excluded in the endpoint application because m>3 and m≤k−1 force adequate positive dimensions. The formal endpoint is not obtained from that vacuity.
4. The analytic seed and pivot hypotheses are the main unproved inputs, not merely bookkeeping lemmas. Any user-facing summary should continue to state the conditional status prominently.

No edits to the reviewed files were made. No blocking defect was found; the concerns above are explicit scope/equivalence obligations for the continuing formalization.
