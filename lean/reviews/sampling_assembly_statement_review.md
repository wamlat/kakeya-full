# Sampling-to-marked-estimate statement review

Read-only review, 6 September 2026, of the frozen `SamplingMeasurableAssembly`, `SamplingPivotInterface`, and `SampledMarkedEstimate`, with their actual normalized probability/support definitions. This is a mathematical interface review, not a repeat of the source/verifier audit. No source was changed.

## Finding

No substantive statement-linkage defect found. In the high branch, the same normalized full/marked arrays, finite support, high-cell set, and single coupled outcome can be passed through both interfaces. The sharpened concentration band really gives factor-two comparable shadings; the original density is recovered with a fixed constant, without a hidden power loss or an unsupported broadness-preserving trimming step. These statements do not yet assert an unrestricted pivot theorem.

## Exact instantiation

For `SampledMarkedEstimate` parameter `k`, use sampling parameter `n=k+1`, hence physical ambient dimension `k+2`. Set:

- `Y=Full`, `E=SamplingSupport.support F.tube Full δ width baseRadius`;
- `cEq=min c₀ 1`, `R=C₀/cEq` (this `R` is a mass ratio, distinct from the physical base-radius parameter);
- `C=SamplingNormalizedMeans.ballCoefficient (k+1)`;
- `p=SamplingNormalizedMeans.full ...` and `q=SamplingNormalizedMeans.marked ...`, with exactly the `high` and `omega` returned by `HighResult`;
- `theta=SamplingTheta.choice (R*K) beta`.

Actual input hypotheses prove `0<cEq≤1`, `R≥1`, `C≥1`, nonnegative `p`, domination of `p` by the original full-cell weights, and `fullMean p i=cEq*lam/δ` for every tube. Both full and marked arrays use the SAME row factor. Thus their nesting, positive cell supports, ball expectations, and total marked-mass bound refer to the same experiment. In particular,

`sum_z markedMean q z ≥ (1/R)*xi*lam*M/δ`.

The returned `SampleGood` and narrow band concern the SAME outcome, rather than separate realizations. With `lamNew=(2/3)*cEq*lam`, the band is exactly

`lamNew/δ ≤ card(fullShade_i) ≤ 2*lamNew/δ`.

The underlying tubes and their indices do not change, so the original separation, cap bound, base bound, `M`, and `A` survive. Mapping support subtypes back to original cell labels is injective and preserves cardinalities. The full union lies in `E`; actual marks are subsets of the full shades and lie in the selected high cells. In this geometric instantiation, selected marks have positive original marked-cell weight. This does NOT mean the full grid cells are pointwise subsets of the original measurable marked sets.

The pivot marked fraction is `xiNew=xi/(8R)`. Its required mass is `(cEq/12)*((1/R)*xi*lam*M/δ)`, which is below the available quarter-total-mean mass. The mark-only angular bound is transferred on these literal marked rows. The full two-ends coefficient becomes `2*4^alpha*C*B`, and geometric width becomes `width+(k+2)/2`. These fixed changes are included in the later uniform constants.

Finally `SampledMarkedEstimate` absorbs the factor `((2/3)*cEq)^pivotDensity` into its constant. Its conclusion uses the ORIGINAL `lam` with precisely the intended density exponent and the original `M,A,δ`. Constants precede all later families, probability arrays and outcomes.

## Explicit remaining hypotheses and boundary

The high-result constructor alone does not provide the full marked-estimate signature. One still supplies the actual original real-cap bound, fixed logarithmic budgets for `B` and the inverse marked fraction, `xi≤1`, and `alpha>0` (the sampling input allows `xi>0` without an upper bound and `alpha=0`). These restrictions are visible, not consequences silently inferred from the sampler. The inverse-angle budget follows from the proved theta lower bound, using fixed coefficient `choice(R*K₀,beta)^(-1)` and exponent `logPower/beta`; it must not be identified with the original raw `K₀` budget.

The sampling alternative also needs small enough scale, `lam≥δ^(1/3)`, `alpha≤1/4`, bounded physical support, separated directions, and actual measurable marked power broadness. Its constants require fixed `c₀,C₀`; scale-dependent normalization constants cannot simply be substituted into those quantifiers.

The low branch produces a count of actual positive low cells, not `SampleGood`. The high estimate bounds the AVAILABLE grid support `E`, not measurable union volume. Applying either branch to angular pieces therefore still needs the actual old-piece support comparison and four-case angular summation, with preservation of the same restricted full/marked unions. The new joint segment/density constructions address this interface; they are not automatically consumed by these three frozen theorems. The unrestricted two-ends removal remains another genuine assembly. The general discrete-to-measurable adapter is already proved once an unrestricted `DiscreteEstimate` has been obtained.

## What the published axioms supply

`ExternalAxioms` gives integer-ambient diagonal estimates: `DiscreteEstimate n (n-1) a a`. The trusted boundary explicitly includes the published maximal-operator-to-normalized-shading consequence. These are not arbitrary real-cap estimates and cannot generally discharge either input `DiscreteEstimate (k+2) m d p` / `DiscreteEstimate (k+3) d d' q`. A full-direction theorem in a larger ambient has the wrong cap/scale exponent for the second input; relabeling its cap parameter would lose a power of scale.

For the first six-dimensional step, however, there is no remaining analytic-seed gap. The exact parameters are original ambient 6, `m=5,d=p=4`, lifted ambient 7, `d'=q=7/2`. `wolff_six` supplies the base. `wolff_five` by itself lives in ambient 5 and would require the manuscript's geometric projection adapter to supply ambient 7. Independently, the already proved `FractionalSeed.fractional_discrete_seed` with `m=4` supplies `DiscreteEstimate 7 4 (7/2) (7/2)` directly; it also supplies that statement in ambient 8, although 8 is not the actual lift of the six-dimensional configuration. Its `m=5` specialization supplies the base as well. The new axioms therefore do not eliminate the present main six-dimensional obstruction.

## Six-dimensional versus whole-paper completion

The checked marked/sampled specialization has set exponent `33/8` and density exponent `15/4`. To reach the manuscript's `M6(33/8)` (arbitrary measurable shadings, uniform positions), one must finish the unrestricted angular globalization, the two-ends removal raising density power to `33/8`, and the final normalization/global-position interface. These are substantial integrations of many existing geometric lemmas, not a numerical substitution; the literal implication is not yet an end-to-end theorem.

For all claimed endpoint bounds, `SeededEndpoint` already proves the scalar iteration and limit passage from the precise UNRESTRICTED real-cap pivot implication; that pivot remains an explicit hypothesis. Completing the general pivot would therefore close a large shared dependency, but the paper's additional maximal-operator restricted-weak/strong interpolation consequences and exact assertion/convention links require their own verification. A defensible status is “the analytic core and seeds are available, with the final globalization layers still open” for the first step, and “broader conditional endpoint machinery is ready, but not all paper results are proved.” A percentage or short completion-time promise would not be supported by these interfaces.
