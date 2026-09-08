# Fixed budgets after anisotropic sampling-input selection

`AnisotropicSamplingBudgets.lean` is clean-built and stable. It has 13 named theorems and four definitions. A full-source audit using the production all-local-declaration command checked 23 environment entries, including 19 theorem entries, without compiler diagnostics. Every entry depends only on `propext`, `Classical.choice`, and `Quot.sound`; no registered or unregistered external axiom is used.

Source SHA-256: `dc259f8a0d276e703d4a1408253286e0d009972391deb76c2e776cfec0f48bae`.

## Fixed coefficients and exact losses

Write `L ≥ 1`, `e₀ > 0`, `q ≥ 0`, and suppose the effective retained fraction satisfies `e ≥ e₀ L^(-q)`, `e > 0`. The module defines

`Cdepth = (|log(4/e₀)| + q)/log 2 + 2`.

This is positive without an extra assumption `e₀ ≤ 1`. From the actual density-selection bound

`D+1 ≤ log(4/e)/log 2 + 2`

the theorem `depth_bound` derives `D+1 ≤ Cdepth L`. The proof uses actual inversion and logarithm monotonicity, then `log L ≤ L`; it does not assume a linear-log depth estimate.

The named constants returned by the frozen `AnisotropicSamplingInput` are bounded literally:

| Returned quantity | Fixed budget |
|---|---|
| `markedFraction e D = e/[4(D+1)]` | `≥ [e₀/(4 Cdepth)] L^(-(q+1))` |
| `endsConstant B e = 4B/e` | `≤ [4B₀/e₀] L^(bLog+q)` |
| `broadConstant angular beta K e D` | `≤ [8 Cdepth broadFactor angular beta K₀/e₀] L^(kLog+q+1)` |

The last two use `B ≤ B₀ L^bLog`, `K ≤ K₀ L^kLog`. The geometric factor is exactly the existing `broadFactor angular beta K₀ = K₀ [8(1+2 angular)^2]^beta`; it has not been silently discarded. Positivity of all four coefficients is proved for `angular ≥ 0`, `B₀,K₀ > 0`.

`uniform_constants` existentially chooses the four positive constants before `L`, `e`, `B`, `K`, and `D`. Thus the permitted dependence is solely on the fixed lower-retention coefficient and exponent, fixed angular/broadness parameters, and fixed original budget coefficients. The component upper-bound lemmas allow arbitrary real `bLog`, `kLog`; applications requiring nonnegative exponents can use the original hypotheses.

## Actual retention interfaces

`retention_budget` shows that if the original piece fraction obeys `eta ≥ eta₀ L^(-q)`, then the actual segment-and-separation-color retention obeys

`retention k angular eta ≥ retention k angular eta₀ * L^(-q)`.

The segment count and palette size remain literal fixed costs in the coefficient. Their positivity is proved from the existing natural-number count theorems.

For the already constructed selected family, the following scalar conversions are available:

* `density_retention`: from `e*lam/4 ≤ lamNew`, obtains `(e₀/4) L^(-q) lam ≤ lamNew`.
* `population_retention`: from `e*M/[16(D+1)] ≤ Mnew`, obtains `[e₀/(16 Cdepth)] L^(-(q+1)) M ≤ Mnew`.
* `density_population_retention`: from the stronger actual inequality `e*lam*M/[16(D+1)] ≤ lamNew*Mnew`, obtains `[e₀/(16 Cdepth)] L^(-(q+1)) lam*M ≤ lamNew*Mnew`.

The third result uses the joint retained-mass bound directly. It does not multiply the separate density and population inequalities, which would unnecessarily double part of the retention loss. Population arguments are nonnegative reals, allowing exact natural-cardinality casts and zero as well.

## Boundary and integration

This module only transforms the actual selection's numerical outputs. It does not perform another selection, replace the retained shadings, assume their desired final estimate, or reprove the measured population inequalities. `AnisotropicSamplingRetention` is the separate actual-geometry adapter providing those inequalities for the same selected family and sets.

The logarithm variable is assumed at least one. When instantiated with `log(2/δ′)`, the small-scale cutoff must ensure this condition; it does not hold automatically for every `δ′ ≤ 1`. If the initial retention and original constants are budgeted using the old mesh logarithm, the separately proved `LowCellAbsorption.log_scale_transport` and `inverse_log_scale_transport` provide the required comparison in the complementary coarse case. This module does not assert that scale relation geometrically.

No frozen module, common Lake file, verifier, registry, or output snapshot was edited.

## Verification artifacts

Commands in the development Lean project:

```sh
lake env lean -o .lake/build/lib/lean/AnisotropicSamplingBudgets.olean AnisotropicSamplingBudgets.lean
lake env lean ../anisotropic_sampling_budgets_axioms.lean
```

The generated full-source audit and actual output are `audit_work/anisotropic_sampling_budgets_axioms.lean` and `audit_work/anisotropic_sampling_budgets_axioms.log`. `audit_work/anisotropic_sampling_budgets_audit.json` records the checked source hash, declaration inventory, and axiom set. The check verifies the exact source prefix, every named theorem's audited presence, absence of forbidden source constructs and compiler diagnostics, standard-only dependency closure, and a fresh compiled `.olean`.
