# Actual first strong operator estimate

`RestrictedStrong.lean` completes the actual first interpolation stage for the literal original-position Kakeya operator. For fixed 0<a<r it explicitly chooses gamma=(r-a)/(2a), so a(1+gamma)=(a+r)/2<r. The positive real coefficient is

`2^(2r) * r * (1-2^(-gamma))^(-a) / (r-a*(1+gamma))`.

`from_restricted_weak` assumes only the actual restricted indicator weak inequality with a nonnegative real coefficient A, for every measurable set and every positive level, then proves the all-measurable-input rth moment estimate with coefficient ofReal(coefficient(a,r)*A). It uses the proved actual PositiveLaws, actual operator measurability, the constructive finite-band dyadic moment theorem, and the actual monotone extension. The two factors 2^r come from the finite level split and dyadic approximation; exact ENNReal/real coefficient normalization includes both. No desired finite-band estimate, abstract operator law, output-measurability, or limiting estimate is assumed at this boundary.

`from_estimate` consumes the actual OperatorRestrictedWeak.Estimate predicate and chooses its positive final C before every mesh delta and measurable input. Its rth moment coefficient is `ofReal(C * delta^(-(n-a+epsilon)))` for actual ambient n=k+1. Every measurable ENNReal input is allowed, including infinite values and integrals. This is the first strong r>a moment estimate; the separate second interpolation stage recovers the source's exponent a.

Clean build with zero diagnostics. Frozen SHA256 b8bae9315921a4a0a950224dd57182fe8c607ee5e2c2c288923ed9c1afeaaf1a. Exact-source audit PASS7 named declarations (2 definitions,5 theorems), standard foundations only, no sorry/custom axiom. Exact source-prefix/hash and declaration checks passed. Audit files/log/meta use RestrictedStrong_full_source_audit.* in audit_work.
