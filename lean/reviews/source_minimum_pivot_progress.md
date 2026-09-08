# Source-minimum marked pivot: actual construction and fourth power

The new modules close the product-versus-minimum and logarithmic-conditioning boundary in the actual marked pivot proof, for the existing analytic range **p ≥ 1**. No product/minimum comparison is used. No B/theta logarithmic budget remains.

## Results

- `AdmissiblePivotSlabs.recovered_selection` applies the genuine generic legal-sample/collision selection to the literal recovered full/marked family. The recovered class density is at least half the original density (`lambda/2 ≤ recovered.density`); original M and E remain in the selected-output lower bound. The exact losses remain sigma > lambda²/(2048 outputConstant) and Q ≥ (outputCoefficient/65536) kappa^[5(ambient−1)] xi² lambda⁸ M² / (sigma² delta⁴ pivotLog(delta)³ E).
- `AdmissiblePivotSlabs.construct` constructs actual original spatial pruning, marked recovery, samples, whole output fibers, every selected slab, original deletion mass, and normalized all-radius spatial bounds for **any supplied admissible kappa**. Its scalar inputs are kappa>0, kappa≤1, 2kappa≤theta, exclusion radius≤1, doubled-B exclusion power≤1/16, and `PivotGeometryScale.Tests`.
- `AdmissiblePivotSlabs.construct_source` discharges those scalar tests for `MinPivotKappa.sourceChoice width B alpha theta`, using only the explicit original cutoff `geometryConstant(ambient,width) * (1+2width)^20 ≤ delta^-1 * kappa^20`. K is fixed before B, theta, alpha, delta and every actual configuration.
- `AdmissiblePivotClosing.energy` invokes actual constructed normalized lifted families, grouped pruning and endpoint closing. It returns rho>0, rho≥lowerCoefficient*kappa^6*sigma and `c*kappa^5*cutoff^-1*rho^r*delta^(d-d'+1+epsilon)*Q ≤ E²`. The fixed geometric factor is absorbed before kappa and the original cutoff are chosen. Its only package-dependent cardinal comparison is the actual recovered-union subset of the original E.
- `AdmissiblePivotClosing.fourth_power` carries that exact package through the original max-cutoff and fourth-power algebra. Its only kappa facts are 0<kappa≤1; no formula for kappa is used.
- `SourceMarkedPivot.admissible_fourth` combines the actual package, actual original base estimate and lifted estimate internally. No assumed sample abundance, selected population, pruning, normalized cap/spatial bound or energy conclusion appears in the input.
- `SourceMarkedPivot.source_fourth` uses the literal source minimum and natural log. `source_union` fixes the absolute cap coefficient A0 and uses the actual original union. `source_notation` is the exact displayed N formulation: mesh=1/N, L=log(2N), S=M/N^m, exponent H=5(ambient−1)+6q+12, scale power N^(2m+3+d'−3epsilon), density power lambda^(p+2q+4+2epsilon), marked power xi^(p+3), and L^(-(p+4)).

## Quantifier and scope check

The final cutoff T and positive c precede N, lambda, M, xi, B, theta, alpha, original tubes and marks. They may depend on the fixed analytic estimates, dimension/exponents, epsilon, width, base radius and fixed original cap coefficient A0. T is the explicit geometry constant above. The source minimum is `c(width)*min(theta,1/100,(c(width)/B)^(1/alpha))`, where c(width)=1/[100(2width+1)], which is a fixed normalization-dependent manuscript-form constant. The original full two-ends coefficient is B; recovered full shadings have 2B, and the minimum's legal power test explicitly accounts for that doubling.

The family/marks hypotheses are actual finite-grid conditions: delta-separated projective directions, fixed-width admissibility, bounded original bases, original real-cap bound, comparable full shadings, marks as subsets, marked mass at least xi lambda M/delta, marked caps of radius theta containing at most one tenth of marked rows, and original full two-ends. We use the fixed concrete normalization of separation delta and comparison interval [lambda/delta,2lambda/delta]. Source `source_notation` takes N≥2 and epsilon∈(0,1]; hence covers the manuscript's epsilon∈(0,1).

**Residual literal-range boundary:** the manuscript allows p>0 in its most general finite statement. These theorems retain p≥1 because the existing coarse-family estimate invokes the cumulative/Jensen adapter (`CoarseFamily.coarse_union_estimate` → `DiscreteEstimate.to_cumulative`). The cutoff algebra's p≥1 premise is also stronger than its scalar use actually needs. Nothing in the new minimum-radius assembly requires p≥1 independently. All recursive applications, where p≥d>1, are covered. Do not describe this as the full p>0 version of Theorem 5.1. No remaining B/theta log-conditioning gap is present in the new fourth-power theorem.

## Source review

The first genuine dependency in the old construction was the call to product-specialized `MarkedPivotSelection.construct` in `PrunedPivotSelection.recovered_selection`; the product was then baked into the dependent `OriginalPivotSlabs.Package` type. Original spatial pruning and marked recovery contain no kappa. Selected slabs, normalization, fixed-pivot cap bounds, grouped lift estimates and closing consume only scalar tests plus the actual constructed data. The new record makes that dependency explicit and supplies the exact same construction at the source minimum.

The fourth-power numeric proof preserves original M, lambda, E, xi; sigma is an actual selected fiber-class size times the original delta. The actual common homothety remains delta/(1+2width), and every normalized perturbation condition is supplied from the same original twentieth-power cutoff. The source-natural-log conversion loses only a fixed coefficient, not a conditioning assumption.

## Validation and freeze

All three production sources compiled with zero diagnostics and were then recompiled from their exact full bytes with every locally named declaration's axioms printed. The audit checked exact source prefix/hash agreement, complete expected declarations, no errors/warnings/sorryAx, and only standard foundations (`propext`, `Classical.choice`, `Quot.sound`).

| Module | Named declarations | SHA-256 |
|---|---:|---|
| AdmissiblePivotSlabs | 5 (3 theorems, 2 records) | `3360ffcde27905cd41fc14f4b3fcadb6d8d949a6898b2a355a514a99e0390b72` |
| AdmissiblePivotClosing | 3 theorems | `862a333a879b4788e3a689c8be5b4eef08586df7d4e0ae83324146ba6691a64d` |
| SourceMarkedPivot | 4 theorems | `8935fef9258325db14d34334d684b693dd364027aa2e9a3518a45925032c1da0` |

Audit evidence: each module has `audit_work/<Module>_full_source_audit.{lean,json,log}`. All three `.olean` files are ready. No frozen source, registry or lakefile was edited.
