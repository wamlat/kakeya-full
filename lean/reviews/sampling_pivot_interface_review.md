# Independent review: sampled marked pivot interfaces

Reviewed read-only: `formalization/SamplingPivotInterface.lean`, `formalization/SampledMarkedEstimate.lean`, and the supporting `SamplingRealization.lean` / `SamplingCapTests.lean` statements. No correctness or quantifier defect found in the reviewed composition.

## Same configuration and outcome

The constructed full family uses precisely the original tube function, original finite support E, and the same outcome omega appearing in SampleGood and the narrow band. The marked shadings use the same high-cell set and omega. Mapping support subtypes to Cell is injective, so all full/marked cardinalities are exact. Directions, separation, cap counts, bounded bases and population M remain unchanged.

Positive selected full probability and `p <= original cell weight` give an actual positive original shading/cell intersection. This yields admissibility at width `width+n/2`; no artificial cell or separate geometric-support premise is inserted. The conclusions concern the finite covering support E, not measurable union volume or a transformed-volume identification.

## Density and marked fraction

The narrow common-mean band gives exactly

`lambdaNew=(2/3)cEq lambda`,

with `0<lambdaNew<=1`, and the strict factor-two Comparable bounds. There is no whole-tube density binning after sampling.

The chosen marked fraction is `xiNew=xi/(8R)`. The marked target is exactly `cEq/12` times `(1/R) xi lambda M/delta`, whereas SampleGood retains at least one quarter of the normalized expected marked mass. Since `cEq<=1`, the stated target is safely below that retained mass. Positivity and `xiNew<=1` follow from `xi>0`, `xi<=1`, and `R>=1`. The lower logarithmic xi budget transfers by the same fixed factor `1/(8R)`.

## Broadness and two ends

Every desired open radius-theta projective cap on an actual marked row lies in an open radius-2theta cap centered at one of its actual tube directions. SampleGood tests all those original directions. No net or unproved broadness of the full shadings is used. Projective symmetry converts the ordering of the two arguments correctly. Broadness holds at all cell labels, with empty rows handled explicitly; hence it holds on the particular union of actual marks required by the core.

The full two-ends coefficient is

`Bnew = (2 * 4^alpha * C) * B`.

The factor four is the actual finite-ball covering enlargement, and factor two comes from the old SampleGood lower density comparison between full mean and realized full count. This is a valid conservative coefficient even though the sharp band would allow factor 3/2. The hypotheses `C>=1` and `alpha>=0` establish `Bnew>=1`. All physical radii from delta to one are covered. The two-ends logarithmic coefficient changes to `(2*4^alpha*C)*B0`, while its logarithmic exponent remains unchanged.

## Uniform estimate constant

`SampledMarkedEstimate.construct` obtains its core constant before M,J, families, measurable sets, E, delta, A, lambda, xi, B, theta, arrays, high cells and outcomes. It calls the all-scales marked theorem at the enlarged fixed width. In ambient dimension k+2, that enlarged width is at least one and therefore meets the core's 1/12 requirement even when the original width is zero.

The final constant is multiplied by `gamma^pivotDensity`, with `gamma=(2/3)cEq>0`. The real-power product identity changes the normalized density back to the original lambda exactly. No scale or density variable enters the fixed prefactor. The linear inverse-cap factor A^(-1) is unchanged.

## Scope and paused next step

These interfaces still accept SampleGood and the sharper band as explicit inputs. Their honest role is to apply the marked core to a compatible sampled outcome; the actual existence of that same outcome is supplied upstream by the new row-normalization and sharp-sampling modules. They do not by themselves remove angular conditioning or full two ends.

Before the task was steered to external theorem verification, the planned next new module was the Section 7 low-cell comparison. Existing `Reduction.angular_factor` already proves the bare favorable tau power, so it should not be duplicated. The missing useful statement is an actual finite low/high dichotomy with a low-support pivot bound, using `m+1-D>0`, `C>=1`, `lambda<=1`, and a fixed lower logarithmic xi budget. The low branch does not require `lambda>=N'^(-1/3)`. Its logarithms can be absorbed by the existing inverse-log theorem at exponent `m+1-D`. A separate old/new log comparison `N<=N'^r`, `r>=1` would transfer original-scale budgets. No new low-cell Lean source had been started when external verification took priority.
