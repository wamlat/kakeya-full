# Independent review of simultaneous diagonal weakening

Read-only review of `DiagonalWeakening.lean`, the actual `ShadedConfiguration.density_ge_half_scale` proof, and the endpoint/rational comparison inputs. No substantive defect found.

For a nonempty tube family, positive density and the lower comparable count force at least one shaded cell on every tube; the upper comparable count then forces delta≤2lambda. This is an actual consequence of positive integer cell counts, not an added analytic hypothesis. The empty-family branch is handled separately.

For d≤D the exact identity is

```
delta^(n-1-d+eps) * lambda^d
 = delta^(n-1-D+eps) * lambda^D * (delta/lambda)^(D-d).
```

Thus the ratio is at most 2^(D-d), and dividing the original uniform constant by that fixed positive quantity proves the smaller diagonal exponent. The proof changes the scale and density powers together. It does not use the invalid general inference that an estimate with density power D immediately yields a stronger smaller density power d.

The coefficient depends only on the fixed exponents and precedes the actual configuration. There are no hidden scale, density, cap or population dependencies. Arbitrary d≤D is mathematically valid for this finite-grid weakening; later measurable conversion separately enforces its own exponent domain.

The six- and eight-dimensional applications use the already proved unrestricted diagonal endpoint. The exact limit values are 7−2sqrt(2) and 11−4sqrt(2), respectively. The checked rational upper bound for sqrt(2) establishes 29/7 and 37/7 lie below them, so both target discrete diagonal estimates follow without a new pivot or seed premise.

Reviewed SHA-256: `4231dbdecbaa784e3ff7bc14adb93c6c10128ac0cc96cce1996fd348f6321860`.
