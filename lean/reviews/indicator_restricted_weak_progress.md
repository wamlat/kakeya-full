# Actual restricted weak estimate from maximal shading

`IndicatorRestrictedWeak.lean` compiles without diagnostics and passes an
exact-source audit: 11 local theorem declarations and one definition, with
standard foundational axioms only. Its frozen source hash is
`2f3e8a0927e83b8e81a6747b3ad57738084566707b0c8db3493876ffeed7efeb`.

For a proved `MaximalShading.Estimate n a`, positive dimension, and every fixed
epsilon>0, `real_bound` chooses C>0 before delta, lambda, the measurable
finite-volume input E, and every supremum witness. It proves

`sigma{K_delta(1_E)>lambda} <= C delta^(-(n-a+epsilon)) lambda^(-a) volume(E)`

in the real measure convention for 0<delta<=1 and 0<lambda<=1.

The proof constructs a delta/2-separated family of actual indicator-level
witnesses with original tube positions. Projective delta-caps cover the entire
level set. The actual cap-measure upper bound is
`B delta^(n-1) M`, and the sum of actual tube volumes is at least
`L delta^(n-1) M`, with B,L positive and fixed by dimension. The shading theorem
at separation coefficient 1/2 controls this sum because every chosen shading is
the literal intersection of E with its tube and their union lies in E. The
common scale/cardinality factor cancels without division by M; M=0 is included.
The uniform constant is B/(c L).

`OperatorRestrictedWeak.lean` extends this result to every measurable E,
including infinite volume, and every positive lambda. It identifies the exact
real indicator supremum with the actual ENNReal maximal operator. Its concrete
six-dimensional 33/8 and all-dimensional algebraic endpoint conclusions require
no supplied analytic or covering premise and use no custom axiom. That module's
separate report and full-source audit record its final source hash.

An independent review of the cancellation, quantifier order, actual geometry,
empty family and finite-measure conversions found no defect; see
`indicator_restricted_weak_independent_review.md`.

This is indicator restricted weak type. General-function strong Lp bounds still
require the remaining interpolation proof.
