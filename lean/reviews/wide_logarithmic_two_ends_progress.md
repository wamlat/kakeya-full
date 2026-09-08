# WideLogarithmicTwoEnds

New standalone `formalization/WideLogarithmicTwoEnds.lean`, source SHA-256 `129fab43489452c389ffa12e7f47c15c35b2384895edc36e41c6ac159eb7c6fa`. Source is frozen; the direct Lean compile and production .olean build both passed with zero diagnostics. Production whole-source dependency audit `WideLogarithmicTwoEnds_operator_audit.json` PASS: one named theorem, one local theorem declaration, one total local declaration; dependencies exactly `propext`, `Classical.choice`, `Quot.sound`. No sorry or custom axiom. No frozen source, lakefile or shared verifier was edited.

`estimate` consumes actual `TwoEndsDiscreteEstimate (k+1) m D C`, m≥0,C≥1. It fixes the original normalization, arbitrary positive lower/upper density multiples c0,C0, B0≥1, alpha>0, logarithmic exponent b≥0 and epsilon>0 BEFORE choosing c>0 and before every actual original TubeFamily, delta,lambda,A and M.

Inputs are original actual admissibility, separation, bounded bases, real-cap bound, lower rows c0*lambda/delta, upper rows C0*lambda/delta, and original full two ends with coefficient B0*log(2/delta)^b. The conclusion is

`c*A⁻¹*delta^(m-D+epsilon)*lambda^C*M ≤ #original union`.

Proof uses `WideTwoEndsEstimate.normalize_rows`: it constructs actual subsets on EVERY original index, all with the same positive integer count and legal new density nu∈(0,1], with nu≥(a/2)*lambda, a=min(c0,1/2). Axes, direction separation, original cap coefficient, bases and admissibility are unchanged; the actual union is a subset of the original union. No marked-broadness assertion is made.

The old/new row ratio is at most C0/a. Therefore the new full two-ends coefficient is bounded by BN*log(2/delta)^b with the FIXED BN=max1(B0*C0/a), chosen before any configuration. The exponent b is unchanged. This uses only positivity of log(2/delta); it does not incorrectly require that B0*log(2/delta)^b≥1 for every delta≤1. The generic `LogarithmicTwoEnds.estimate` already works without that per-configuration condition. Applying it and using nu≥(a/2)*lambda pays only the fixed factor (a/2)^C, preserves the original density power C, and retains the same original A,delta,M and union.

The result handles empty families and the one-cell/very-small-density regime through the existing actual ceiling trim, rather than excluding lambda comparable to or below delta. It remains a theorem on unit axes with arbitrary fixed geometry; scalar agent owns the new actual fixed-original-length/log-budget transport and the final six-dimensional fixed-convention source consumer. This source is outside frozen checkpoint23's418 modules; final source-scope publication requires later integrated verification.
