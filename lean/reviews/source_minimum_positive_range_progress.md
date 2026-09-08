# Full positive-p source-minimum pivot

**The residual p≥1 restriction is removed.** `SourceMarkedPivotFullRange.source_notation` proves the actual original-union fourth-power bound for every p>0, with the literal manuscript-form minimum, the exact source powers, natural logarithm, and only the original N*kappa^20 cutoff. No B/theta logarithmic budget remains. No contradiction/vacuity argument, altered density exponent or new analytic axiom is used.

## Why p>0 works

The relevant coarse family already has a lower bound on **every** tube's shading. Its old use of the arbitrary-shading cumulative/Jensen estimate was unnecessary. `LowerDensityEstimate.lower_density` chooses the actual integer K=ceil(s/delta), trims every shading to exactly K cells, and uses the existing geometric density normalization. When s>0 and M>0, K>0 and K does not exceed any original shading cardinality. The normalized comparable density is at least delta*K/(2*gridCountConstant), hence at least s/(2*gridCountConstant). Raising this inequality to p only requires p≥0. The s=0 and M=0 branches are proved directly; p>0 gives 0^p=0.

This adapter invokes `Cumulative.subfamily_bound`, whose proof explicitly constructs the selected subsets and normalizes them and already assumes only p≥0. It does not invoke `DiscreteEstimate.to_cumulative`, finite-bin Jensen, a weighted average-density inequality or any claimed cumulative estimate for p<1. Its constant depends only on the original estimate and fixed normalization; there is no bin count, log loss or dependence on s.

`PositiveDensityPruning.coarse_union_estimate` applies that adapter to the genuine cap-thinned coarse family. The per-tube density premise is exactly `CoarseFamily.selected_coarse_density`, derived from original admissibility and the actual fine-to-coarse fiber count. The cumulative record used to transport geometry has its cumulative field derived by summing those same per-tube inequalities; no extra population or density hypothesis is added. The coarse lower bound has the same A^-1*delta^m*r^(-d+epsilon)*s^p*M powers as before.

## Actual downstream construction

- `PositiveDensityPruning.discrete_heavy_mass_bound` reuses the actual heavy-cell excess contradiction with the new coarse estimate. Its threshold remains K*E*A*delta^(d-m-epsilon)*eta^(-(p+1))*lambda^(-p)/M.
- `discrete_spatial_pruning_budget` constructs literal original survivors at every dyadic scale and sums actual deletion mass, with the same log-depth and no additional loss.
- `marked_recovery` constructs the same injectively reindexed recovered full/marked family, preserving original comparison M and E, factor-two density choice, actual marked mass and marked-only broadness.
- `PositivePivotSlabs.construct` and `construct_source` fill the **frozen** `AdmissiblePivotSlabs.Package` with the resulting original pruning, samples, output fibers, actual slabs and normalized spatial geometry. The radius remains supplied admissible kappa, or the actual `MinPivotKappa.sourceChoice` under its original twentieth-power cutoff.
- `PositivePivotAlgebra` generalizes only three scalar proofs. The max-cutoff bound uses p+1≥0; the natural-log comparison uses p+4≥0. The fourth-power composition uses these new lemmas and the same actual package. It does not change any density, kappa or scale exponent.
- `SourceMarkedPivotFullRange` composes the actual construction, unchanged `AdmissiblePivotClosing.energy`, original base estimate and lifted q+epsilon estimate. All populations and endpoint-energy inputs are derived internally.

## Final exact statement and scope

For the explicit original finite-grid model and fixed width, base radius and absolute cap coefficient A0, the final `source_notation` chooses T,c>0 before N, lambda, M, xi, B, theta, alpha and the original tubes/marks. At mesh delta=1/N, N≥2, it proves

    E^4 ≥ c * kappa^[5(ambient−1)+6q+12] * xi^(p+3)
             * log(2N)^(-(p+4)) * N^(2m+3+d'−3epsilon)
             * lambda^(p+2q+4+2epsilon) * (M/N^m)^3,

where E is the cardinality of the actual original full union and kappa is exactly

    c(width) * min(theta, 1/100, (c(width)/B)^(1/alpha)),
    c(width) = 1/[100(2width+1)].

The sole fine-scale premise is T≤N*kappa^20, with T=geometryConstant(ambient,width)*(1+2width)^20. No comparison with the product choice is involved. Original B is doubled only in the actual recovered two-ends condition, and `source_admissible` explicitly handles 2B. The coefficient c is also uniform in alpha; the statement allows any alpha>0, so includes the manuscript's alpha≤1 range.

The analytic inputs remain the actual base `DiscreteEstimate ambient m d p` and lifted `DiscreteEstimate (ambient+1) d d' q`, with p>0 and q≥2. The geometric construction requires m≥0,d≥0 and ambient=k+2; these include the source range 1<d<m≤ambient−1 and d'>0. The full/marked input is the same actual fixed normalization as before: delta-separated projective directions, shadings in [lambda/delta,2lambda/delta], fixed-width admissibility, bounded bases, actual cap bound, marked fraction and marked cap condition, and original full two-ends. No caller-supplied pruning, sample, selection, count, spatial, cap-thinning or energy oracle remains.

This closes the previously reported positive-p caveat in `source_minimum_pivot_progress.md`; that earlier report and its three frozen source files remain unchanged. It does not claim a new general cumulative estimate with p<1, which the argument neither needs nor proves.

## Validation

All five new production files compiled with zero diagnostics. Exact full-source audits printed every named theorem's axioms, verified the current source hash and exact source prefix, checked complete name coverage, and rejected errors, warnings, sorryAx or any nonstandard axiom. All 14 local theorems passed using only `propext`, `Classical.choice`, and `Quot.sound`.

| Module | Theorems | SHA-256 |
|---|---:|---|
| LowerDensityEstimate | 1 | `c357f66c0746e5a7ddc56be78f645d2279cf07aef3b5b3b96cf078f7c652e367` |
| PositiveDensityPruning | 4 | `666082e06446b170190f5a297c99988f64227b6871879de15b12414d152416a6` |
| PositivePivotSlabs | 2 | `e7be65a12a35958332fd0c6a76066337c0003de9ffa14ec1ece9c1278ecef078` |
| PositivePivotAlgebra | 3 | `1ea6cc701aebc8f971bb272216e93a25091739e1205cec97eeddd8f72da6eee3` |
| SourceMarkedPivotFullRange | 4 | `dfcd7b86dd15da7a60b511dfcd4ca59846e6a3867bb746c8b16c75f105c645fc` |

Evidence: `audit_work/<Module>_full_source_audit.{lean,json,log}`. All five `.olean` files are ready and source bytes frozen. No previously frozen source, registry or lakefile was edited.
