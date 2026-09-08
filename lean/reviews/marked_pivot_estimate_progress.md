# Actual original marked pivot estimate

Development module: `formalization/MarkedPivotEstimate.lean`.

This module composes `OriginalMarkedPivot.construct` with `PivotLossAbsorption`. The caller does **not** supply a fourth-power estimate, a collision-energy bound, selected lift witnesses, or a lower bound for kappa. All of those intermediate requirements are supplied by the actual original-configuration construction and the explicit kappa choice already formalized upstream.

## Exact conclusion and uniformity

Write

`D = (2m+3+d')/4`, `C = (p+2q+4)/4`.

The small-scale theorem `construct` fixes positive `delta0,c` before the family, finite covering set E, marked shadings, mesh delta, cap coefficient A, density lambda, marked fraction xi, two-ends coefficient B, or angular radius theta is supplied. It concludes

`c A^(-1) delta^(m-D+epsilon) lambda^C M <= |E|`.

The ambient dimension is `k+2`, and the lifted estimate is in `k+3`. The required analytic inputs are precisely `DiscreteEstimate (k+2) m d p` and `DiscreteEstimate (k+3) d d' q`, with `m,d >= 0`, `p >= 1`, `q >= 2`. Fixed width is at least `1/12`; fixed base-radius normalization is explicit.

The theorem `all_scales` gives the same estimate for every `0 < delta <= 1` under the same original marked hypotheses. It uses the actual cap-population and one-tube coarse bound above the constructed threshold, taking the minimum of two fixed positive constants.

The outer parameters include positive `B0,K0,xi0,alpha`, nonnegative `bLog,qLog,xLog`, and arbitrary positive final error epsilon. The original hypotheses retain:

- Comparable nonempty finite shadings, `0 < lambda <= 1`, actual delta direction separation, actual cap bound, admissibility and bounded bases.
- Actual markings contained in each original shading, total marked incidence at least `xi lambda M/delta`, and pointwise marked broadness at theta (at most one tenth of incident marks in every open projective cap).
- Full original two-ends at every physical radius from delta to one, with coefficient B and exponent alpha.
- `B >= 1`, `0 < theta <= 1`, `0 < xi <= 1` and fixed budgets `B <= B0 log(2/delta)^bLog`, `theta^(-1) <= K0 log(2/delta)^qLog`, `xi >= xi0 log(2/delta)^(-xLog)`.
- E is any finite covering set containing every full original shading; it need not equal their union.

## Derivations inside the composition

1. The absorption theorem chooses its input error `e = min(1/2,epsilon/4)` before invoking the actual fourth-power construction. The resulting raw positive constant may depend on e. Final thresholds and constants are then chosen before configurations.
2. The actual construction uses `kappa = PivotKappa.choice width (2B) theta^(-1) alpha 1`. Applying `choice_log_lower` with the recovered two-ends coefficient `2B` proves

   `kappa >= kappa0 log(2/delta)^(-(bLog/alpha+qLog))`,

   where `kappa0 = PivotKappa.choice width (2B0) K0 alpha 1 > 0` is fixed. No additional kappa premise appears in the final estimate.
3. The actual raw fourth-power estimate uses `pivotLog delta`. The theorem `natural_log_fourth` converts it to the common natural logarithm, multiplying the raw constant by the positive fixed factor `(3/log 2)^(-(p+4))`.
4. The original family is turned into an actual `ShadedConfiguration` with the same mesh, density, cap constant, family and population. Its finite comparable shadings imply `lambda >= delta/2`. Its actual projective cap estimate implies `M delta^m <= packingConstant(k+1) A`. Neither bound is an external input.
5. `PivotLossAbsorption` removes all fixed logarithmic losses, uses finite density to absorb the `2e` density error, takes the fourth root, and uses the cap-dependent population bound to retain a linear `A^(-1)` coefficient.
6. The minimum of the raw-construction threshold and the absorption threshold is positive and independent of every configuration variable.

## Scope relative to the manuscript

This closes the source Section 5.8 consequence for the original marked, transverse, full-two-ends class with explicit polynomial logarithmic budgets. The final density exponent is exactly C: this is slightly stronger than the displayed `C+epsilon` variant for `lambda <= 1`, because the verified finite-density lower bound absorbs the density error into the scale loss.

The implementation uses the existing **product** kappa choice. It does not assert that this choice is comparable to the manuscript's minimum choice, or that its logarithmic exponent equals the minimum-choice exponent. The proved exponent is the sum `bLog/alpha+qLog`; this fixed larger log loss is absorbed without changing D or C.

Angular conditioning to obtain these markings and budgets, and the later removal of the original two-ends assumption, are still separate tasks. This is not an unconditional `DiscreteEstimate` pivot theorem or a final endpoint proof. No uniformity as alpha tends to zero is asserted; the exponents D,C are independent of alpha, while constants can depend on it.

## Verification

Lean 4.33.1 and mathlib commit `0df444a360eaa60ab8c11dca51a86af692955474`. Final compile and full-source axiom audit results will be recorded below.

Final verification: all five theorems and both proof-bearing configuration definitions clean-compile. The current olean is built and the full-source audit prefix matches the final source. All seven declarations were audited and use only standard Lean foundations (propext, Classical.choice, Quot.sound); no proof placeholders, custom axioms, errors, warnings, or residual tactic diagnostics occur. SHA-256: `93c402ffb4b23de883a584f7e186d7635609f1b6b5f72143ada1c5daf48d0b07`.

Commands from `audit_work/formalization`:

```
/Users/ssoh/.elan/bin/lake env lean -o .lake/build/lib/lean/MarkedPivotEstimate.olean MarkedPivotEstimate.lean
/Users/ssoh/.elan/bin/lake env lean ../marked_pivot_estimate_axioms.lean > ../marked_pivot_estimate_axioms.log
```
