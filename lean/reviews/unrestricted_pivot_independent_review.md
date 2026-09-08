# Independent statement review of UnrestrictedPivot

Read-only review of `UnrestrictedPivot.lean`, linked against the actual `TwoEndsPivot.from_base_and_lift`, `TwoEndsGlobalization.remove_two_ends`, `SeededEndpoint` and `Endpoint` statements. No substantive defect or circular dependency found.

`real_cap_pivot` uses the source domain `3<d'<d<m`, `d≤p`, `d'≤q`. For every adequate integer ambient n, it derives n≥2, writes n=k+2, and applies the base estimate in that same ambient and the lift in ambient n+1. The lifted cap exponent is d, and its adequacy follows from d<m≤n−1. No ambient lift estimate is assumed at the original cap exponent m.

The source domain implies all actual two-ends pivot conditions: m≥1, p≥1, d≥0, q≥2; output set exponent is below m; both output exponents are at least one. The sparse-branch margin is `(p+2q+5−3d')/12`, which is strictly positive under p≥d>d' and q≥d'. Globalization then returns the exact maximum of the output set and density exponents, with all configuration quantifiers already enforced by `DiscreteEstimate`.

The two endpoint theorems supply this proved pivot to the existing constructive recursive endpoint. The seed comes from `FractionalSeed`; the stage is selected using only epsilon before any configuration in `Endpoint.of_limit`. Thus neither endpoint retains a supplied pivot, marked/two-ends condition, sampling oracle or new external axiom. The diagonal endpoint is restricted to integer n≥6 because this is where the limiting set exponent exceeds four and absorbs the density envelope. It does not claim the dimension-five diagonal endpoint.

The conclusions are exact finite discrete predicates. This file does not by itself assert the measurable/maximal interpretation; that requires the separately proved measurable conversion and the precise normalization/position domain of its predicate. The unused import of `MeasurableEstimate` adds no mathematical hypothesis to these declarations.

Reviewed SHA-256: `724ccc29a18566f85f3f928b742e10a901b0b4596646b3106bb9b381bdbb0722`.
