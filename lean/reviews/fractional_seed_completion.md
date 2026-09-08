# Fractional seed completed; endpoint now conditional only on pivot

## Main checked statements

`FractionalSeed.fractional_real_cap_seed` proves, for every real m>3:

`RealCapEstimate m ((m+3)/2) ((m+3)/2)`.

There is no analytic estimate, seed, angular decomposition, two-ends reduction, direction-selection oracle, rounding hypothesis, or incidence bound among its premises. `RealCapEstimate` is the actual predicate from Configurations: for every adequate integer ambient dimension, every fixed normalization and every epsilon>0, one positive constant is chosen before delta, lambda, A, M and the full actual Euclidean tube/grid configuration.

`SeededEndpoint.real_cap_endpoint_from_pivot` and `SeededEndpoint.diagonal_endpoint_from_pivot` supply this proved seed to the existing endpoint iteration. Their only analytic hypothesis is the exact stated pivot estimate. The n>=6 diagonal endpoint is therefore **still conditional on pivot**. These wrappers do not prove pivot and do not certify the PDF's final endpoint unconditionally.

## New frozen module list for checkpoint10

| Module | Theorems | Role |
|---|---:|---|
| LocalizedDirectionThinning | 5 | Actual complete-shading coarse direction selection; target separation; smaller-scale cap tests; one original A^-1 loss |
| LocalizedSeedNormalization | 6 | Common unit dilation; actual legal density from local tube count; exact shading/union cardinalities |
| FiniteGridLocalization | 5 | Actual common radius and density classes on original Euclidean cell centers |
| FiniteLocalizedFamily | 11 | Exact selected-index family; cap and ball properties; two logarithmic class budgets; actual radius-density inequality |
| SeedCoverNormalization | 10 | Initial fixed common dilation establishing every full-shading unit-ball cover |
| LocalizedSeedApplication | 3 | Direct application of the proved two-ends seed to the actual normalized/thinned family |
| SeedGlobalizationAlgebra | 5 | Exact radius-to-density powers and choice of localization exponent |
| CoveredSeed | 2 | Actual unrestricted-family seed with explicit small density error and two logarithms |
| FractionalSeed | 4 | Final uniform error absorption and exact discrete/real-cap fractional seed |
| SeededEndpoint | 2 | Endpoint and n>=6 diagonal wrappers conditional only on pivot |

Total: 53 new theorems in 10 modules after checkpoint9. The prior 9 angular seed modules in checkpoint9 contain 86 theorems; the combined seed construction is 139 theorems in 19 modules. These are additional module counts, not a replacement for the root verifier's whole-package census.

## Construction and parameter accounting

1. Dilate every original shading by the same fixed factor C=1+max(1,width), about one zero-grid origin. Unit axes are shortened and extended in their original directions. Full shadings now fit unit balls. Both scale and density divide by C; original union cardinality is exact. Cap testing at the smaller scale is proved using the original cap endpoint, with no larger cap coefficient.
2. Select an actual common dyadic radius rho and an actual common local-density class. Their combined retained tube count is at least M/[(alpha+3)L(delta)^2], independent of lambda. All selected local shadings consist of original cells, retain rho^alpha of original mass, and have all-center two-ends tests.
3. Full cap hierarchy selection followed by an actual fixed-palette coloring selects complete localized shadings and yields target direction separation. At dilation L=K rho it retains at least M rho^m/[T(k,m) A] and a cap coefficient depending only on k,m.
4. Choose K as the maximum of 8 max(1,width) and the explicit local tube-ball population coefficient. Every original short tube embeds in a genuine new unit tube, and the new comparable density s/(K rho) is at most one by the proved local population count. All tubes use the same spatial homothety. Their bases may vary freely because the actual two-ends seed does not require bounded bases. No spatial cluster loss or distinct-origin comparison is used.
5. Apply the fully proved angular/hairbrush two-ends seed. The direct localized inequality is c A^-1 delta^((m-3)/2+epsilon) s^2 rho^((m-1)/2) M<=original localized unioncard. The original cap coefficient occurs only through the thinning loss; the new family uses a fixed cap coefficient.
6. Actual geometry gives lambda<=C_local rho^(1-alpha). Together with s>=rho^alpha lambda this produces exactly the density exponent d/(1-alpha), d=(m+3)/2, in the global covered-family estimate.
7. Choose eta=epsilon/3 and alpha=eta/(d+eta), so d/(1-alpha)=d+eta. For nonempty finite integer shadings, comparability proves lambda>=delta/2. This finite fact and the checked seed-logarithm absorption pay for the extra eta density exponent and the two logarithms, contributing 2eta scale error in addition to the seed's eta. The total is exactly epsilon. Empty families are handled separately.
8. Undo the initial common dilation. Its scale and density factors combine to exactly C^(-(m+epsilon)), a fixed positive constant.

No original direction-separation or bounded-base assumption is needed in the stronger covered-family proof: the actual cap selection constructs the necessary separation. The final ShadedConfiguration theorem retains the standard predicate and its usual hypotheses. No finite-density lower bound is asserted for arbitrary measurable shadings.

## Verification

Lean4.33.1; configured mathlib commit 0df444a360eaa60ab8c11dca51a86af692955474. Each module was clean-compiled and its `.olean` built in the development project. Full-source audit files append `#print axioms` for every theorem; the audit source prefix was compared with the current source. All ten modules, including SeededEndpoint, have exact current audit sources, clean built oleans, no errors/warnings, and only propext, Classical.choice, Quot.sound. All 53 theorem audits completed successfully.

Commands from `audit_work/formalization`:

```
/Users/ssoh/.elan/bin/lake env lean -o .lake/build/lib/lean/FractionalSeed.olean FractionalSeed.lean
/Users/ssoh/.elan/bin/lake env lean ../fractional_seed_axioms.lean > ../fractional_seed_axioms.log
/Users/ssoh/.elan/bin/lake env lean -o .lake/build/lib/lean/SeededEndpoint.olean SeededEndpoint.lean
/Users/ssoh/.elan/bin/lake env lean ../seeded_endpoint_axioms.lean > ../seeded_endpoint_axioms.log
```

Individual full-source audit filenames follow the snake_case module name with `_axioms.lean` and `_axioms.log`, under audit_work. Root's forthcoming frozen full-build/environment audit and the independent geometry-agent review provide additional checks. The completed proof above establishes the fractional seed; all remaining pivot hypotheses remain explicit in SeededEndpoint.
