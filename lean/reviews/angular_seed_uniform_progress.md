# Uniform actual finite two-ends seed

`AngularSeedLogLoss.lean` (13 theorems) and `AngularSeedEstimate.lean` (4 theorems) compile cleanly; full-source axiom audits on all 17 theorems use only `propext`, `Classical.choice`, and `Quot.sound`. Their development oleans are built. These extend the seven frozen modules documented in `angular_seed_groups_progress.md`, for 86 new seed-assembly theorems across nine modules.

## Final statement

`AngularSeedEstimate.two_ends_seed` chooses a positive constant **before** every tube count M, actual family F in ambient k+2, physical scale delta, shading density lambda, actual two-ends coefficient B, and cap coefficient A. The fixed inputs are width, alpha>0, beta>0, beta<=(m-1)/2, B0>=1, b>=0, m>=1, and epsilon>0.

For all such actual families, with 0<delta<=1, 0<lambda<=1, A,B>=1, B<=B0 L(delta)^b, actual width-delta admissibility, comparable lambda/delta shading size, delta-separated directions, the actual m-cap bound with coefficient A, and full original finite two-ends tests for every center and delta<=r<=1, the theorem proves:

`c A^(-1) lambda^2 M delta^((m-3)/2+epsilon) <= F.unionCells.card`.

Here `L(delta)=logb 2 (2/delta)+2`. The theorem constructs the actual angular assignment internally and handles empty M. It has no angular grouping, hairbrush, rounding, supplied analytic estimate, or bounded tube-base premise. The original two-ends assumption remains explicit.

## Uniformity and arithmetic

Actual angular depth satisfies J+1<=L. The retained fraction obeys rate>=rateBase/L and eta>=etaBase/L with rateBase=3/(8 C_(k+1)) and etaBase=rateBase/4. The logarithmic exponent is `AngularBoxLogLoss.logarithmicLoss(k,alpha,beta,b,0,1)+1`, independent of shading density. The extra one is the retained tube-count cost. The true A^(-1/2) dependence of the box constant is proved exactly and weakened uniformly to A^(-1) for all A>=1. All actual logarithms are absorbed using an explicitly quantified positive epsilon-loss constant.

## Checks and scope

Commands, from `audit_work/formalization`:

```
/Users/ssoh/.elan/bin/lake env lean -o .lake/build/lib/lean/AngularSeedLogLoss.olean AngularSeedLogLoss.lean
/Users/ssoh/.elan/bin/lake env lean -o .lake/build/lib/lean/AngularSeedEstimate.olean AngularSeedEstimate.lean
/Users/ssoh/.elan/bin/lake env lean ../angular_seed_log_loss_axioms.lean > ../angular_seed_log_loss_axioms.log
/Users/ssoh/.elan/bin/lake env lean ../angular_seed_estimate_axioms.lean > ../angular_seed_estimate_axioms.log
```

Toolchain: Lean4.33.1, configured mathlib commit 0df444a360eaa60ab8c11dca51a86af692955474.

Remaining unrestricted seed assembly: actual common-radius/common-density localization, coarse direction thinning and exact common unit-tube rescaling, radius-density power absorption, and removal of the small density/exponent errors. Because this proved two-ends seed needs no bounded-base premise, all localized short tubes can use one shared spatial homothety regardless of their localization centers. No spatial-cluster overlap loss is needed in this route. The target Endpoint seed is only for m>3, where a fixed positive beta <=(m-1)/2 exists. The m=1 case is not claimed here and is irrelevant to that Endpoint premise.
