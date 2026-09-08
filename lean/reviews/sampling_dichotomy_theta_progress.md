# Sampling low/high split and angular radius (Section 6)

SamplingDichotomy.lean and SamplingTheta.lean are frozen, clean-built to .olean. A fresh combined source audit checks all 13 local declarations and reports only the standard axioms propext, Classical.choice and Quot.sound. No warnings, sorry or custom axioms.

SamplingDichotomy defines the literal low cells by 0 < mu(c) < cutoff and high cells by cutoff <= mu(c). For every nonnegative finite expected-mass array and positive cutoff, it proves exact mass partition even though zero cells are omitted from low. It then constructs the disjunction: the positive low cells carry at least half of total expected mass and number at least total/(2 cutoff), or the actual high cells carry at least half. marked_dichotomy instantiates mu with SamplingApplication.markedMean q. This establishes (6.6)/(6.13) with non-strict high-half inequality, which suffices for the sampling theorem and its final quarter-mass conclusion. No partition or high-mass condition is supplied as an assumption.

SamplingTheta uses exactly theta = min(1/100, (1000 K)^(-1/beta)/2). For K,beta positive it proves positivity, theta <= 1/100 and 1000 K (2 theta)^beta <= 1. For L >= 1, A >= 0 and K <= K0 L^A it proves theta(K0,beta) L^(-A/beta) <= theta(K,beta), with the fixed prefactor positive. The minimum causes no lost logarithmic exponent because L^(-A/beta) <= 1.

uniform_choice chooses N0 before N,K and every configuration; uniform_small_scales expresses the same result as delta0 > 0, delta0 <= 1 before delta,K. Under K <= K0 log(2/delta)^A and delta <= delta0, it returns delta <= 2 theta <= 1, exact cap budget and the explicit log lower bound. K >= 1 is not needed: K > 0 suffices. The source threshold is therefore fully uniform under the stated fixed logarithmic growth budget. No cap net is assumed. Parent SamplingCapTests uses actual original directions as finite test centers; the expectation budget here applies to their radius 2 theta.

Remaining composition is in SamplingMeans, SamplingRealization and the final original-input count-or-discretize wrapper. These modules do not assert that arbitrary means came from geometric shadings; the geometric mean interface is explicitly the separate SamplingMeans task.

Validation files: sampling_dichotomy_compile.log, sampling_theta_compile.log, sampling_dichotomy_theta_full_source_audit.lean and .log.

SHA-256:
- SamplingDichotomy: 09af644a52bb4eef38b60064401dd0a3c494c64b9a0ed0dcb145097ca9a68ce3
- SamplingTheta: b4081e86e43250d5c73b2978137b0edfe5196db955c2f655439a5a18a45a3cf0
