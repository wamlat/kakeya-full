# Explicit logarithmic losses for the actual one-box estimate

`AngularBoxLogLoss.lean` is complete and compiled without warnings: 10 theorems and 2 definitions. It imports the clean constructed one-box result and the clean actual hairbrush logarithm lemmas. No mathematical input was replaced by an axiom.

The main theorem, `single_box_logarithmic`, has the same actual geometric and measurable inputs as `AngularBoxAlgebra.single_box_quadratic_density`, together with explicit scalar budgets

`η ≥ η₀ L^(−q)`, `B ≤ B₀ L^b`, `K ≤ K₀ L^c`, and `hairbrushLog(k,δ) ≤ logCoefficient(k)L`.

Here η₀, B₀, K₀, and L are positive. It derives the actual original-union bound

`C_log L^(−P) λ² M δ^(k+1)(δ/τ)^((m−1)/2) ≤ volume(⋃ Ref_i)`.

The exponent is formally identified as

`P = (k+1)(b/α+c/β) + q[(k+1)(1/α+1/β)+5/2] + 5/2`.

For nonnegative b, c, q and positive α, β, `logarithmicLoss_nonneg` proves P is nonnegative. There is no density dependence in P. The constant `C_log` is the positive `logarithmicConstant`, depending only on k, angular width, η₀, α, β, B₀, K₀, m, and A, with no λ, δ, τ, M, L, b, c, or q dependence.

Writing `e₀=η₀/(segmentCount·paletteSize)` and `H=8(1+2a)²`, the constant is

`radiusConstant(k,4B₀/e₀,8K₀H^β/e₀,α,β) e₀^(5/2) / [16 allScaleConstant(k) sqrt(A')]`,

where `A'=packingConstant(k+1) A H^m`, and the imported `radiusConstant` includes the factor `logCoefficient(k)^(−5/2)`.

The intermediate lemmas derive the recovered coefficient bounds with exponents `b+q` and `c+q` from the original budgets. The retained density contributes the separate exponent `(5/2)q`. `angular_prefactor_log_lower` proves that the original δ logarithm budgets the entire normalized scale δ/τ, using the proved monotonicity of the actual hairbrush logarithm. Thus the theorem introduces no additional assumed logarithm bound at an angular-dependent scale.

Verification used a clean `.olean` compilation and `AngularBoxLogAudit.lean`, which prints every new theorem's axiom list. All are subsets of the standard `propext`, `Classical.choice`, and `Quot.sound`. This module completes the one-piece logarithmic accounting; global angular grouping, summation of original unions, and the final fractional `RealCapEstimate` remain separate construction and integration work.
