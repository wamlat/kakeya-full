# Separate review of the original marked first-power estimate

Reviewed `MarkedPivotEstimate.lean`, its report `marked_pivot_estimate_progress.md`, and the relevant definitions and called statements in `OriginalMarkedPivot`, `OriginalPivotSlabs`, `PivotLossAbsorption`, `CoarseBounds` and `Configurations`. No mathematical or statement-level defect was found in this bounded review. This is a review of the conditional marked estimate, not a claim that the later angular or two-ends reductions are finished.

## Actual hypothesis boundary

The analytic inputs are explicitly `DiscreteEstimate (k+2) m d p` and `DiscreteEstimate (k+3) d d' q`. These are the actual all-normalization finite configuration estimates, including inverse cap coefficient, not a symbol concealing an assumed pivot bound. The original hypotheses retain comparable full integer shadings, original delta separation and cap bound, bounded bases, full admissibility, marks contained in the original full shadings, marked mass, marked one-radius broadness, and full physical two ends. Broadness is tested on the marked incidence rows only; no full-row broadness is inferred.

The nonempty original population, positive density, lambda≤1, xi≤1, positive B0/K0/xi0/alpha, and fixed logarithmic upper/lower budgets are all visible. The covering set E need only contain all original shadings. There is no supplied sample system, selected fiber, closing energy, desired E^4 bound, population estimate, finite-density lower bound, or kappa lower budget in the public theorem.

## Constants and exponents

All geometric normalizations, analytic exponent parameters, conditioning budgets and the desired error epsilon precede the existential constants. The absorption error `e=min(1/2,epsilon/4)` is chosen before the actual raw fourth-power constant is requested. The raw threshold, raw constant, absorption threshold and final constant are consequently fixed before any family, marks, E, delta, A, lambda, xi, B or theta is supplied. Taking the minimum of the two positive thresholds preserves that uniformity.

The exact raw errors are 3e in delta and 2e in lambda. Integrality and comparability derive lambda≥delta/2 from one genuinely nonempty shading. The density error therefore costs 2e more in delta. Absorbing the fixed logarithmic loss costs another 2e, for 7e in the fourth-power exponent. The proved inequality 7e≤4epsilon suffices after taking the fourth root. There is no unrecorded density loss: the final power is C=(p+2q+4)/4.

Actual cap geometry gives S=M delta^m≤C_dim A. The root bound has A^(-1/4) S^(3/4); population linearization gives at least a fixed multiple of A^(-1/2) S, then A≥1 permits weakening to A^(-1) S. Thus the reported inverse cap coefficient is valid, although it is not the strongest scalar consequence. Finally S=M delta^m accounts for the exact exponent delta^(m−D+epsilon), D=(2m+3+d')/4.

The `pivotLog` to natural-log comparison is used in the correct direction: a positive upper bound on the log gives a lower bound on its negative power. Its constant is fixed and positive. No assumption log(2/delta)≥1 is silently used; positivity is sufficient where the log-budget identity is invoked.

## All physical scales

For delta below the fixed threshold, `all_scales` changes only the scale field of the actual original hypotheses and invokes the fine theorem. Above it, `CoarseBounds.coarse_configuration_bound` uses an actual tube's lower count lambda/delta, the actual cap population bound, lambda^C≤lambda (C≥1), and the bound delta^(1−D+epsilon)≤max(1,delta0^(1−D+epsilon)). This argument handles either sign of 1−D+epsilon. Its fixed coefficient matches the one used in `all_scales` exactly. The actual union is included in E using the original covering field. No sampled or transformed union is substituted for E.

## Kappa convention and report accuracy

The implementation consistently uses the product `PivotKappa.choice width (2B) theta^(-1) alpha 1`. Its logarithmic lower exponent is exactly bLog/alpha+qLog, derived with the actual recovered coefficient 2B. Neither the proof nor its report reverses a product/minimum comparison or claims the literal minimum-kappa Theorem 5.1. The report clearly retains the original marked and two-ends assumptions and the fixed polynomial logarithmic budgets; it does not claim an unconditional pivot estimate or endpoint theorem.

The source report's improvement from C+epsilon to C is justified by the finite-density argument above. Its lack of uniformity as alpha tends to zero is also correctly stated. The exponents D and C are independent of alpha; the constants and thresholds may depend on it.

## Verification inspected

The source SHA-256 is `93c402ffb4b23de883a584f7e186d7635609f1b6b5f72143ada1c5daf48d0b07`, matching the report. The existing full-source audit begins with the exact current source and audits all seven declarations (five theorems, two proof-bearing definitions). Its log contains no errors, warnings or sorry axioms; its exact axiom union is `propext`, `Classical.choice`, `Quot.sound`. This review did not edit the source or rerun an unchanged already-passing build.

## Concrete next geometric bridge

Section 6 physical pages 25–27 needs actual expectation identities and bounds for the same finite sampling law. `SamplingSupport` supplies finite positive-cell support and valid cell-intersection probabilities. `SamplingBallTests` supplies finite tests and their arbitrary-ball cover; `SamplingCapTests` is assigned separately for direction-centered angular tests. The complementary next module is `SamplingMeans`: prove exact sums of the actual intersection weights equal normalized measurable mass, bound ball-test means by normalized mass in an enlarged physical ball and derive the two-ends bound including enlarged radii above one, and integrate marked pointwise angular broadness over a cell to bound cap-test means. These are the actual geometric/measure inputs still exposed in `SamplingApplication.finite_sampling_assembly`; no additional probabilistic inequality is needed for this bridge.
