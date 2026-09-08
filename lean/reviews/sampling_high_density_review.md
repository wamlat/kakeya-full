# Independent review: actual sampling, high-density pivot, and original cells

Reviewed on 2026-09-06. No mathematical statement or parameter-accounting defect was found in the reviewed versions. This is a read-only independent review; no production source was edited.

## Sources and verification

The principal modules were read in full, together with the relevant actual-input, sampling, realization, row-normalization, scalar-absorption, and transformed-grid-support interfaces. Each principal source was independently rechecked with `lake env lean <module>.lean` using the project's matching dependencies; all three returned exit 0 with no output or warnings. This review did not repeat the full package build or replace the package's all-declaration axiom audit.

| Module | SHA-256 |
|---|---|
| `SamplingMeasurablePivot.lean` | `a7897e130bd6950409f5715038e4a898e775237dc7e7d8661aa989d76f88030b` |
| `SamplingHighDensity.lean` | `38f190d7ddacfef7783bdb417d88b0a3b438f2858f80ad63129c518f84e482ef` |
| `SamplingOriginalCells.lean` | `b7fb8229519e4e3a6c2c17fc34c7fee11c59fb6deb49b567890e66eb5b0f8bd4` |

The additional scalar source `LowCellAbsorption.lean` has SHA-256 `2b2ca55ea8d1be69659ed256e2df823b5d7364d0d7cc6122fd48e5530c2672bc`; its separate proof/axiom audit is recorded in `low_cell_absorption_progress.md`. The earlier detailed sampled-family review is in `sampling_pivot_interface_review.md`.

## Actual input and one common sampling outcome

`SamplingNormalizedMeans.Input` contains measurable full and marked sets, carrier containment, bounded axes, positive compatible density parameters, upper/lower full masses, total marked mass, physical-ball two ends, and almost-everywhere marked broadness. It contains no probability arrays, sample outcome, concentration result, desired support lower bound, or expected pivot conclusion. Its positive family count excludes the trivial empty-family case explicitly.

The actual support is `SamplingSupport.support`. Original cell weights are the corresponding full or marked cell-intersection volumes divided by cell volume. Both arrays are normalized by the same per-tube multiplier. With `cEq = min c₀ 1` and `ratio = C₀/cEq`, the full row mean becomes exactly `cEq*lam/δ`, while nestedness `0 ≤ q ≤ p ≤ 1` and domination by the original full-cell weights are preserved. Total marked mean loses at most the fixed factor `1/ratio`. The cap-mean loss is the same fixed ratio; it is included in the chosen angular cutoff.

In the high alternative, `SamplingMeasurableAssembly` supplies one `omega` on these exact normalized arrays, simultaneously satisfying `SampleGood` and the narrower full-count interval `[2/3 mean, 4/3 mean]`. `SamplingMeasurablePivot.low_or_pivot` passes those same arrays, high set, ball masks, cap masks, and outcome to `SampledMarkedEstimate`. The narrow interval is rewritten using the actual exact-row-mean theorem. There is no change of sample or independently selected favorable event between concentration and geometric realization.

The previously audited `SamplingPivotInterface` constructs the realized family and its literal marked-pivot hypotheses. Its density is `(2/3)*cEq*lam`, its marked parameter is `xi/(8*ratio)`, and its two-ends multiplier is `2*4^alpha*ballCoefficient`. These fixed costs are absorbed by `SampledMarkedEstimate` before configuration-dependent variables are introduced. Density binning is not used to assert broadness preservation.

## Uniform constants and angular budget

The sampling scale cutoff and pivot constant are existentially chosen before the actual family, sets, tube count, mesh, density, marked fraction, variable broadness/two-ends constants, and cap constant. Their permitted dependencies are the fixed analytic estimates and listed fixed geometric/exponent/log-budget parameters.

For `L = log(2/δ)`, the actual angular choice obeys

`theta ≥ choice(ratio*K₀, beta) * L^(-kLog/beta)`.

The inverse-budget lemma correctly turns this into

`theta⁻¹ ≤ choice(ratio*K₀, beta)⁻¹ * L^(kLog/beta)`.

The fixed row-normalization ratio is already inside the choice. Positivity is proved before inversion, the division sign in the exponent is correct, and the sampling construction gives the needed `δ ≤ 2*theta ≤ 1`. The original `B`, `K`, and `xi` budgets remain fixed-log budgets, with no hidden dependence of the final constant on their actual values.

The high-density cutoff is `(1/δ)^(-1/3) ≤ lam`. The uniform concentration estimates were proved with non-strict inequalities, so equality at the cutoff is permitted. The dimensions match throughout: these wrapper modules use ambient dimension `k+2`, and therefore invoke the preceding sampling module with parameter `k+1`.

## Low/high combination

The low alternative gives a lower bound for a subset of the actual support type. `card_le_univ` and the subtype cardinality identity bound that low-cell count by the cardinality of the actual support. No additional support-cardinality assumption is introduced.

Its literal coefficient is

`cLow = 1 / (2 * ratio * highCoefficient (k+1))`.

The rational-expression conversion to `cLow*xi*lam*M/(δ*log(2/δ))` is exact. `uniform_low_cap_bound` uses the explicit strict margin `pivotSet m d' < m+1`, the positive epsilon, and the proved density exponent `pivotDensity pExp qExp ≥ 1`. The latter follows from `pExp ≥ 1`, `qExp ≥ 2`. It absorbs the inverse-log marked fraction with a genuine positive power of the mesh. Since `lam ≤ 1`, replacing `lam` by its required higher power is legitimate. Since `A ≥ 1`, introducing `A⁻¹` weakens the low lower bound.

`SamplingHighDensity.construct` chooses `min cLowResult cPivot > 0` before the configuration. Both branches are weakened using an explicitly nonnegative common factor. Thus the final estimate is obtained from the actual alternatives, rather than assuming a favorable branch or supplying the target estimate as an input.

The later additions `input_weaken_alpha` and `all_exponents` are correct. On the tested radius range `δ ≤ r ≤ 1`, decreasing a nonnegative exponent increases `r^alpha`. The record update changes only the exponent and the corresponding physical-ball proof; all measurable sets, masses, broadness, and geometry are unchanged. `all_exponents` chooses `min(alpha,1/4)` before the uniform constants. Consequently its public statement, and the final original-cell wrapper, permit every fixed `alpha > 0` without a public `alpha ≤ 1/4` restriction.

## Original-cell support comparison

`SamplingOriginalCells.construct` applies the bound at the normalized mesh `δ/tau`. It then uses the proved `TransformedGridSupport.positive_support_card`, assuming literal containment of every full set in the common anisotropic image of the old cell union.

The comparison factor is exactly `(2*(k+2)+3)^(k+2)`, the dimension-only factor in the actual ambient dimension. The final constant is divided by this positive factor before the old mesh, angular scale, map, old cell set, and configuration are quantified. The natural-number cardinal bound, real cast, and positive multiplication cancellation all preserve the inequality direction.

The underlying grid theorem covers every genuinely touched new cell by a finite integer box around each old cell image. Positive-measure support is a subset of the touched cells. Its proof uses the actual Lipschitz bound of the map, `W ≥ 1`, and `0 < tau ≤ 1`. Boundary intersections are included. No normalized-volume equality, inverse-`tau` cell-count loss, or overlap bound for pulled-back new grid cells is presumed.

## Exact remaining boundary

These results are small-normalized-scale, high-density estimates for inputs with actual marked broadness and two ends. The original and lifted `DiscreteEstimate` premises remain genuine analytic prerequisites. The strict dimension margin, positive fixed exponent assumptions, cap/separation hypotheses, normalized log budgets, and original-image containment are explicit.

The final wrapper does not itself construct the preceding angular/spatial pieces, prove their fixed-log budgets, settle the sparse-density or complementary-scale branches, or sum pieces into an unrestricted estimate. Those are the remaining upstream/downstream assembly obligations. In particular, its log budgets are at `δ/tau`; transporting original-mesh budgets still requires the separately proved scale relation and log-transport lemmas.
