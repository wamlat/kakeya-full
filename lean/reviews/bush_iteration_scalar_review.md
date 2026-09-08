# Independent review: actual Appendix A bush iterations

Read-only statement/proof review found no defect in these frozen sources:

- `formalization/BushIteration.lean`: SHA-256 `8077245382f010bec470501c8085ffa9fc7f163b4805bc683f444a7587142e90`.
- `formalization/BushIterationConsequences.lean`: SHA-256 `198d1fcc8443790e431513e19aafd9cda013bf54608ed519e5e52f31ad274798`.

I compared the full sources with combined.txt Appendix A.2/A.3, lines
1975–2050, and checked the invoked scalar-domain lemmas, density globalization,
and finite-depth endpoint transfer. I did not repeat the separate production
source/dependency audits.

The actual lifted family has ambient dimension n+1: after n=k+2 the lift
is `DiscreteEstimate (k+3) d ...`. The original seed is the bush estimate with
cap exponent n-1, giving d0=(n+1)/2. Every later stage invokes the actual bush
lift and the positive-density pivot/globalization pipeline. A marked-family
construction, angular output, two-ends conclusion, or endpoint is not an
unproved stage premise. The direct pivot does not impose the narrower
recursive d'>3 restriction, which would incorrectly exclude early stages.

For A.2, the lift uses d'=q=(d+2)/2 and yields D=(4n+d+4)/8 and C=(d+3)/2.
For A.3, `weaken_set` changes only the lifted set exponent to (d+1)/2;
q remains (d+2)/2. Its monotonicity direction is correct for delta in (0,1]:
decreasing the set exponent increases the power of delta and weakens the
lower bound. It does not replace the density exponent.

The checked domains hold for every integer n>=5 and all iterate values
between d0 and the relevant limit. They establish q>=2, D<m=n-1, D>=1,
positive sparse-density margin, and C<D. Hence the actual globalization's
density exponent max(D,C) is D, as required. The empty population remains
covered by the underlying estimate predicates.

The finite recurrences are the actual estimate inductions with ratio 1/8,
not merely numerical sequences with assumed analytic stages. In both limits,
`DiscreteEstimate.of_limit` chooses a finite stage after the requested epsilon
but before any configuration, then invokes that stage at epsilon/2.
Consequently constants remain uniform in delta, lambda, A, tube count, and
positions. The endpoint limits (4n+4)/7 and (4n+3)/7 are reached with arbitrary
positive scale loss, without requiring constants uniform in iteration depth.

The consequence module invokes `MainMaximal.from_diagonal` only as the
generic proved measurable and arbitrary-position adapter. Its conclusions
are the precise `MaximalShading.Estimate` predicate. They are not operator-norm
claims, and the stronger main endpoint is not substituted for the bush route.
