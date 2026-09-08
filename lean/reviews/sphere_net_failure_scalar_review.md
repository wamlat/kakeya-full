# Independent review: literal sphere-net failure probability

Read-only mathematical review found no defect at these frozen source hashes:

- `formalization/SphereNetFailure.lean`: SHA-256 `3667726a67e39c9766916bc246bc5b4fde4d721892e53d8f074bfefc6d73735a`.
- `formalization/SphereNetSourceFailure.lean`: SHA-256 `36e453b75585065954290a11affb96e5d09db74f32afc638bbf0cc491043fc09`.

This review inspected the complete source statements and proofs, including
the source theta inversion, actual test count, and logarithmic tail estimate.
It does not duplicate their separate production source/dependency audits.

The law in both modules is the same coupled three-state product law for the
original nested arrays p,q. `angularFailure` includes both the marked total
lower-tail event and each marked-cap upper-tail event on every high cell.
The index type `high × Option Caps` gives exactly
`high.card*(1+Caps.card)` tests; the additional marked-cell event is counted.
Each actual test has its proved Chernoff bound. Overlapping tests are combined
by a finite union bound, without assuming independence between them.

The thresholds are deliberately non-strict bad inequalities, so they enlarge
rather than shrink the bad event relative to a strict source convention.
The cap upper threshold is old markedMean/20, and its actual cap mean is at
most old markedMean/1000. The full marked-cell threshold is old markedMean/2.
This gives the stated common exp(-cut/8) bound, including empty high sets and
arbitrary finite cap populations.

`test_count_threshold` obtains the actual spherical net bound from packing
and polylog absorption. Fixed spatial P and the extra 1 are both absorbed
before the actual net/high cells are supplied. It proves the literal
N^(ambient+2) count. `source_tail` uses the same
64*(ambient+4) coefficient and natural log(2N); its final estimate by 1/16
for N>=16 is strictly below 1/8. There is no missing fixed multiplicative
factor outside the earlier threshold.

`source_angular_failure` constructs the actual entire-sphere net and original
finite support from `SamplingLengthInput`. Its high set is defined using
exactly `rawMarked` on that support, and `rawLaw` uses exactly `rawFull` and
`rawMarked` without row normalization. The theta lower bound from
`SamplingTheta.uniform_small_scales` is inverted using positive theta0 and
positive log(2/delta), yielding the correct power logPower/beta with fixed
coefficient 1/theta0. The source theta upper and lower testing ranges are
proved at the same cutoff.

Actual support geometry bounds high.card. Original almost-everywhere marked
broadness supplies each doubled-net-cap mean through `source_cap_test` on the
same original support. Neither a mean estimate, net count, good outcome, nor
desired probability bound is a field of the final public premise. The final
threshold is chosen before all families, probability arrays, scale, density,
and variable K. Density and full-ball failure events remain separate, as the
module statements explicitly say; the joint probability needs their bound
on this same raw law.
