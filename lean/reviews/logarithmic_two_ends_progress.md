# Uniform original logarithmic two-ends coefficients

Frozen source: `LogarithmicTwoEnds.lean`, SHA-256 `569da09b05110e964f820042b223f08b1ba0ed42f3a9dbf0aa2a972c5d0cf075`. It compiled with zero diagnostics using Lean 4.33.1 and the pinned mathlib project. The exact-source dependency audit is recorded separately in `logarithmic_two_ends_audit.json`.

The source requirement is first-step PDF Lemma 6, extracted `first_step.txt` line 432: its two-ends coefficient may grow logarithmically with the original scale. The previous fixed-B all-angle estimate does not imply this uniform statement by merely substituting a varying B. The new theorem supplies that missing implication geometrically.

`LogarithmicTwoEnds.estimate hestimate hm hC geom B0 alpha b eps hB0 ha hb heps` takes a proved `TwoEndsDiscreteEstimate (k+1) m D C`, m nonnegative and C at least one. For every fixed normalization, B0 at least one, positive alpha, nonnegative b and positive eps, it chooses one positive c before every original `ShadedConfiguration`. Its only added original-family condition is full relative two ends with coefficient `B0 * log(2/delta)^b`. The conclusion is

`c * A^(-1) * delta^(m-D+eps) * lambda^C * M <= #unionCells`.

The density exponent remains C. There is no assumed localization outcome, radius budget, retained population, cap estimate, or analytic-energy output. No varying coefficient is passed to the uniform analytic input.

For small original mesh, actual localization at beta = alpha/2 supplies a subfamily and ball restrictions. `radius_constraint` combines the original full-row upper count, the selected row lower count and the original all-ball test at the actual selected radius. It proves `1 <= 2*B*rho^beta`. This uses the stored selection's actual statements, with the fixed factor two; it does not posit a stronger original-row fraction.

`LogarithmicTwoEndsAlgebra.density_factor` then pays the explicit loss power q = max(0, beta*C+D-C)/beta. This handles positive or negative combined radius exponents. `LocalizedTwoEndsApplication.localized_bound` applies the analytic input at the fixed coefficient `4^beta` on genuinely normalized groups. The original selected population costs `log(2/delta)^(-2)`. The combined logarithmic power b*q+2 is absorbed by half of the prescribed scale error, with constants chosen before the configuration. The actual coarse configuration bound handles the remaining scales and the empty-family branch is explicit.

The parent owns `SixDimensionalLogarithmic.lean`, which specializes this result to D=33/8 and C=15/4 and exposes the literal source N/S notation. That separate final signature is the direct first-step Lemma 6 consumer. Neither this new generic theorem nor its specialization alters any of the earlier frozen sources.

Validation command (from the development project):

```
lake env lean -o .lake/build/lib/lean/LogarithmicTwoEnds.olean LogarithmicTwoEnds.lean
python3 ../audit_logarithmic_two_ends.py
```

The second command recompiles the complete unchanged source with the production environment-wide axiom audit. Its JSON gives the exact final hash and dependency result. Integrated checkpoint verification remains the parent's separate gate.
