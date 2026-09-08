# Actual real-cap measurable endpoint and exact diagonal limits

`MainEndpoint.lean` is frozen and clean-built. Its12 theorem declarations compose the now-proved fractional seeds, unrestricted real-cap pivot, finite-stage recursive iteration, endpoint loss allocation, and actual measurable conversion.

The generic `real_cap_measurable` theorem proves, for every real m>3,

`RealCapMeasurableEstimate m (limitProfile m) (max (limitProfile m) 4)`.

The real-cap predicate quantifies every adequate positive integer ambient dimension; the constant is fixed before every actual configuration. The full density envelope is retained when it differs from the set exponent. The endpoint is strictly above3 by the proved positive scalar slope.

For each integer n≥6, `diagonal_discrete`, `diagonal_measurable`, and `diagonal_volume` give the exact equal set/density exponent

`D_n = limitProfile(n−1) = 3+(2−sqrt2)(n−4)`.

The diagonal simplification is justified by the proved inequality D_n>4. It is not silently extended to lower dimensions or to every real-cap parameter.

`bounded_maximal` derives the cap-free maximal-shading formula in every fixed bounded position normalization. Actual direction separation supplies the full ambient cap coefficient, whose inverse is absorbed in the fixed constant. There is no arbitrary input cap bound or coefficient in this predicate.

Exact specializations are provided for finite, measurable, and cap-free bounded maximal estimates in dimension6 at7−2sqrt2 and dimension8 at11−4sqrt2. These use the existing verified Scalar.dimension_six_limit and Scalar.dimension_eight_limit identities, rather than decimal approximations.

## Precise scope

No seed, pivot, angular, marked, sampling, localization, full-two-ends, or published-result axiom is supplied as a premise to these endpoint theorems. The dependency audit confirms standard foundations only. The cap-free maximal declarations explicitly concern fixed bounded positions. The separate constructive measurable spatial reduction is required to derive MaximalShading.Estimate, which has no bounded-position premise; this module does not claim that conversion prematurely.

## Verification

```
lake env lean -o .lake/build/lib/lean/MainEndpoint.olean MainEndpoint.lean
lake env lean ../main_endpoint_axioms.lean
```

Both produced zero diagnostics. The exact full source plus the production all-local-declaration collector was checked. All12 named source theorems and14 local environment theorem declarations use only propext, Classical.choice, and Quot.sound. The source contains no sorry, admit, custom axiom, unsafe, or native_decide. Exact SHA/hash is recorded in `main_endpoint_audit.json`; complete evidence is `main_endpoint_axioms.lean` and `.log`.

Toolchain: Lean4.33.1; mathlib `0df444a360eaa60ab8c11dca51a86af692955474`.
