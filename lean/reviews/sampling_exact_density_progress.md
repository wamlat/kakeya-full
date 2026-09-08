# Exact density normalization before sampling

New modules: `formalization/SamplingRowNormalization.lean` and `formalization/SamplingExactDensity.lean`.

The sampled interval in the manuscript, `[c0 lambda/(2 delta), 2 C0 lambda/delta]`, need not have ratio two. The existing marked pivot core requires the exact `Comparable` interval `[lambdaNew/delta, 2 lambdaNew/delta]`. Selecting a whole-tube density class after sampling does not automatically preserve its one-tenth marked broadness. These modules close that interface by equalizing expected full counts **before** sampling and proving a sharper full-count concentration interval. Every original tube index is retained; no density-bin broadness claim is made.

## Actual row normalization

Let `mu_t = fullMean p t`, choose `mu > 0` with `mu <= mu_t <= R mu`, and define the explicit arrays

`factor p mu t = mu/mu_t`,

`full p mu t c = factor p mu t * p t c`,

`marked p q mu t c = factor p mu t * q t c`.

`SamplingRowNormalization` proves:

- `1/R <= factor <= 1` and the factor is positive.
- The actual new probabilities remain nested in `[0,1]`.
- Both new probabilities are pointwise below the old probabilities, and positivity of each is equivalent to positivity of the corresponding original probability. The original positive-measure support therefore remains the exact available support.
- Every new expected full count is exactly mu.
- New expected marked multiplicity and total marked mass are at least `1/R` of the old quantities.
- Every expected full ball count is exactly its old value times the row factor. An old relative ball bound `ballMean <= K*mu_t` becomes `newBallMean <= K*mu` with no additional loss.
- Expected marked cap count is at most the original cap count. If the old relative cap bound is K, the new relative cap bound is `R*K`. This is a fixed loss applied to the expected angular bound before choosing the tested angle.

For the actual source bounds `c0 lambda N <= mu_t <= C0 lambda N`, choose

`cEq = min(c0,1)`, `mu = cEq lambda N`, `R = C0/cEq`.

The theorem `source_parameters` proves these bounds from `0<c0<=C0` and positive lambda,N. The retained expected marked fraction is therefore `cEq/C0`, with no scale, density, or population dependence.

## Sharper actual coupled concentration

`SamplingExactDensity.poisson_binomial_narrow` derives

`Pr[X <= (2/3)mu or (4/3)mu <= X] <= 2 exp(-mu/100)`

from the actual moment-generating-function bound. It uses exponential Markov at `t = +/- log(4/3)`, with verified rational bounds on that logarithm. The constant `1/100` is conservative and explicit. The proof is a multiplicative mean-dependent bound, so it remains useful for sparse incidences.

`coupled_test_narrow` instantiates it on the existing genuine finite coupled full/marked law. `finite_sampling_narrow` constructs one positive-support outcome with **both**:

1. Every original `SamplingApplication.SampleGood` field, including one-tenth angular broadness, ball-test control, quarter-total marked mass and full/marked positive-support guarantees.
2. The sharper per-tube interval `[(2/3)fullMean p t, (4/3)fullMean p t]`.

The same outcome carries both sets of guarantees. The sharper lower and upper density bounds imply the old SampleGood density bounds; no separate outcome or independence claim is used.

## Uniform scale threshold

`uniform_sampling_narrow` removes the numerical sharp-budget premise and chooses N0 before every finite index type, scale, probabilities, masks and configuration variable. `source_sampling_narrow` specializes it to the same actual dimensional counts and source mean/cutoff hypotheses as `SamplingThreshold.source_sampling`, with `a0=64(n+4)` and the proved mean powers `N^(2/3)` and `N^(5/12)`.

Only the full-density failure rate changes from `2 exp(-mu/12)` to `2 exp(-mu/100)`. All ball and angular rates remain unchanged. An arithmetic identity writes the new rate budget as the old numerical budget with its full array multiplied by `3/25`; this is used **only to compare real-valued rate sums**. The sampling law always uses the actual nested p,q, never that auxiliary array, which need not satisfy nesting with q.

The threshold depends solely on fixed dimensional/count/expectation coefficients. There is no caller-supplied failure probability, successful realization or sharp density assertion.

## Exact bridge to the marked core

With equalized full mean `mu=cEq lambda/delta`, the sharp interval is exactly the strict Comparable interval at

`lambdaNew = (2/3)cEq lambda`.

`SamplingRowNormalization.comparable_of_narrow` applies to the actual realized `TubeFamily`, proves `0<lambdaNew<=1` when `0<lambda<=1`, and proves `family.Comparable delta lambdaNew`. The full sampled family and its marks have already been constructed on every original tube; no tubes are binned or dropped.

Quarter-total marked sampling retention gives at least `xi lambda M/(4 R delta)` whenever the original marked expectation is at least `xi lambda M/delta`. The root assembly uses the safe normalized marked fraction `xiNew=xi/(8R)`; its compatibility with lambdaNew is a separate short scalar substitution there. The angular factor `R` is absorbed in the expected cap coefficient before sampling, so the eventual one-tenth fraction required by the original marked core is unchanged.

## Remaining dependencies

The finite probability and density-normalization mismatch is closed. The separate geometry assembly must instantiate the row-normalization hypotheses from actual measurable cell weights and original density/two-ends/broadness bounds, then apply the existing positive-support grid realization. The geometry agent owns `SamplingNormalizedMeans`; the root owns `SamplingPivotInterface`. Those modules must use the same normalized arrays and the same sharp outcome. Angular decomposition and the later two-ends reduction remain outside this result. No original-core or frozen file was changed.

## Verification

Toolchain: Lean 4.33.1; mathlib commit `0df444a360eaa60ab8c11dca51a86af692955474`. Row normalization has fourteen theorems and three definitions. Exact density has eight theorems and one definition. Final clean build and full-source axiom audit results are recorded below.

Final verification: both current oleans are clean-built. All 26 declarations were checked in full-source audits matching the final source prefix. Dependencies use only standard foundations (propext, Classical.choice, Quot.sound). There are no proof placeholders, custom axioms, errors, warnings, or residual tactic diagnostics.

- `SamplingRowNormalization.lean`: 17 declarations audited, SHA-256 `cb6aa2839b152897ecf443dc52907220a5f7fb3e13fe67f66371c4fed0211c1f`.
- `SamplingExactDensity.lean`: 9 declarations audited, SHA-256 `05a9a541b8f30b899bcd5ef13ff2dd5b3e9f3936f4f65214264ca0e7cad85ebc`.

Commands from `audit_work/formalization`:

```
/Users/ssoh/.elan/bin/lake env lean -o .lake/build/lib/lean/SamplingRowNormalization.olean SamplingRowNormalization.lean
/Users/ssoh/.elan/bin/lake env lean -o .lake/build/lib/lean/SamplingExactDensity.olean SamplingExactDensity.lean
/Users/ssoh/.elan/bin/lake env lean ../sampling_row_normalization_axioms.lean > ../sampling_row_normalization_axioms.log
/Users/ssoh/.elan/bin/lake env lean ../sampling_exact_density_axioms.lean > ../sampling_exact_density_axioms.log
```
