# Uniform sampling probability threshold

New development module: `formalization/SamplingThreshold.lean`.

The missing scalar step was the sentence in Section 6 asserting that all polynomially many density, ball, and high-cell angular tests succeed simultaneously for sufficiently large N. `SamplingApplication` already proved the coupled probability model and Chernoff bounds, but its application theorem required `failureBudget < 1`. This module derives that bound from the actual count and expectation interfaces and constructs a simultaneous `SampleGood` outcome. No failure probability, successful realization, or desired sample conclusion is assumed.

## Main concrete theorem

`KakeyaFormal.SamplingThreshold.source_sampling` chooses `N0 >= 1` from fixed ambient dimension n and fixed count/expectation coefficients `CT,CB,CE,cf,cb` (count coefficients nonnegative, expectation coefficients positive). The threshold precedes **all** finite index types, their instances, the scale N, masks, probabilities, density lambda, two-ends coefficient B, exponent alpha, and actual configuration data.

For every `N >= N0`, the theorem takes actual finite tube, cell, ball-test and cap-test types, full probabilities p, nested marked probabilities q, a finite set of high cells, actual Boolean ball/cap masks and cutoff/radius functions. Its numerical hypotheses are exactly:

- `0 <= q <= p <= 1` at each tube-cell coordinate.
- Tube count at most `CT N^(n-1)`.
- Ball-test count at most `CB N^n (log N/log 2+1)`.
- High-cell count at most `CE N^n`.
- Cap-test count at most the tube count; all original tube directions can be used as cap labels.
- `lambda >= N^(-1/3)`, `B >= 1`, `0 <= alpha <= 1/4`, and every test radius is at least `1/N`.
- Full expected tube count at least `cf lambda N`.
- Each cutoff at least `cb B r^alpha lambda N` and at least four times its actual expected ball count.
- Every high cell has expected marked multiplicity at least `64(n+4) log(2N)`.
- Every high-cell cap expectation is at most one thousandth of that cell's expected marked multiplicity.
- High cells contain at least half the total expected marked mass.

The output is an actual finite outcome `omega` with `SamplingApplication.SampleGood`: per-tube density bounds, all ball-test upper bounds, high-cell lower multiplicity, one-tenth angular cap bounds, quarter-total marked mass, nesting, and positive-probability support of all selected full/marked incidences. These are the already proved `SampleGood` fields, constructed by the coupled finite law.

No upper budget on B is needed to make this probability threshold uniform: larger B only increases the ball cutoff. Its logarithmic upper budget is still needed later for applying the marked pivot estimate.

## Derived powers and actual number of tests

`source_mean_powers` proves, rather than assumes,

`lambda N >= N^(2/3)`,

`B r^alpha lambda N >= N^(5/12)`.

It uses only the source density cutoff, B>=1, r>=1/N, and alpha<=1/4. There is no sub-mesh two-ends condition.

`source_counts` starts with the separate actual tube, ball, high-cell, and cap cardinal bounds. It bounds tube-ball pairs by

`CT CB (1/log 2+1) N^(2n)`

and high-cell plus high-cell/cap tests by

`CE (1+CT) N^(2n)`.

This deliberately uses all original directions as cap tests rather than presuming the manuscript's theta-net construction. The same explicit dimensional threshold `a0=64(n+4)` suffices: `a0/8=8n+32 > 2n`. Ambient n controls these test counts, independently of the real direction-cap exponent m.

## Uniform probability argument

`uniform_threshold` proves a threshold for the sum

`2 CT N^u exp(-cf N^eta/12)`

`+ CB N^v exp(-cb N^phi/4)`

`+ CH N^w exp(-a log(2N)/8)`.

For arbitrary fixed real u,v,w, positive eta,phi,cf,cb, nonnegative CH,a and `w<a/8`, it is strictly below one above a fixed N0. The first two terms tend to zero by a proved substitution in Mathlib's polynomial-times-exponential limit. The third is bounded by `CH N^(w-a/8)`, whose exponent is negative. The threshold is extracted from the proved limit; it is not an unproved asymptotic assertion or a supplied failure-budget bound.

`uniform_sampling` places that threshold before even the finite index types and calls the actual finite sampling construction after deriving its exact failure budget. `source_sampling` instantiates this theorem with the two proved expectation powers and the explicit dimensional test counts.

## Exact remaining dependencies

The scalar probability threshold is now closed. The final geometric sampling assembly must still instantiate the following with the **same** actual support, weights, masks, and output family:

1. `SamplingSupport` supplies all positive-measure support cells, their actual bounded-grid cardinality, and the nested cell probabilities. The sum of cell weights must be identified with the normalized full and marked measures.
2. `SamplingBallTests` supplies actual finite ball masks, their radius/count bounds, and the conversion from test bounds to all physical balls. Their expected counts must be bounded using the original measurable two-ends condition and fixed cell enlargement.
3. Actual cap masks centered on original tube directions must have the required one-thousandth expected marked fraction, and every desired radius-theta cap must be contained in one such tested cap when occupied. The finite agent is separately formalizing the literal theta choice and its uniform mesh threshold.
4. The low/high dichotomy must provide either the low-cell count or the high-half-mass input. This is also assigned to the finite agent.
5. The sampled family, comparable-density normalization, marked fraction, unchanged separation/cap geometry and support comparison must be assembled into the exact input record for `MarkedPivotEstimate`. No unconditional angular-normalized pivot or final endpoint theorem is claimed here.

## Verification

Lean 4.33.1; mathlib commit `0df444a360eaa60ab8c11dca51a86af692955474`. The module has nine theorems. Final compile and full-source axiom audit results follow below.

Final verification: all nine theorems clean-compile, the current olean is built, and the full-source axiom audit prefix matches the final source. Every theorem uses only propext, Classical.choice, and Quot.sound. No proof placeholders, custom axioms, errors, warnings, or residual tactic diagnostics occur. SHA-256: `c64bdcd365558f0614745d17ce0ad1842a673912bd963a14bf5352e81053e717`.

Commands from `audit_work/formalization`:

```
/Users/ssoh/.elan/bin/lake env lean -o .lake/build/lib/lean/SamplingThreshold.olean SamplingThreshold.lean
/Users/ssoh/.elan/bin/lake env lean ../sampling_threshold_axioms.lean > ../sampling_threshold_axioms.log
```
