# Same-outcome source realization from full-sphere sampling tests

`SphereNetSampleRealization.lean` is frozen and its production `.olean` compiles with zero diagnostics. The exact-source audit PASS covers 19 named theorems, 36 local theorems and 53 all-local declarations, with only `propext`, `Classical.choice` and `Quot.sound`. Source SHA: `ad372c13817b22b97aa1474638d07d2def201d2c708aaafa29df9a65b67747b8`. It is outside the already published 381-module checkpoint 21.

## Output and actual outcome

The public type is

    Output F Full G delta width R L B alpha theta net

where `net : ProjectiveSphereNet.Net n theta` is the actual full-sphere net in ambient dimension `n+1`. Its fields are exactly `depth`, `bottom`, `bottom_upper`, `depth_bound`, `omega` and `good`. The `good` field is `SampleGood` for the original raw `SamplingLengthInput` probabilities, original high set, actual ball masks/cutoff and `SphereNetCapTests.cap net F`. There is no narrow-density field and no second sample.

`of_sample net J hb hu hd omega good` packages exactly the supplied outcome. This is a generic geometric realization adapter: the separate probability argument must construct that outcome and its `SampleGood` certificate. The module does not assume a different favorable outcome to obtain any geometric conclusion.

## Original geometry and support

`Output.family` and `Output.marks` use the existing injective unlabeling of finite support subtypes back to their original integer grid labels. `axes` is definitional equality to each original tube; `separated`, `cap_bound` and `bounded` preserve the same original directional and position conditions, including any fixed separation multiple.

`support_and_marks`, `union_card` and `cell_union_subset` prove containment in the same available grid support and marked-row containment in the full row. Selected whole cells are not claimed to lie inside the original measurable shading. Instead, `full_positive` and `marked_positive` prove their own actual positive full or marked intersection, respectively.

With the original `SamplingLengthInput.Input`, `admissible` derives a legal parameter in the original interval `[0,length_i]` and distance at most `(width+ambient/2)*delta` from the unchanged axis point. This uses actual positive intersections and the grid-cell center distance. `longitudinal_count` gives the fixed mesh-interval count with the same explicit grid constant and no alignment assumption.

## Literal source mass and broadness

Only the broad `SampleGood` band `[fullMean/2,2*fullMean]` is used. `density` therefore gives the source original constants

    c0*lambda/(2*delta) <= #full_i <= 2*C0*lambda/delta.

`marked_mass` retains one quarter of the exact original total marked mass divided by `delta^ambient`; `marked_density` gives the corresponding `xi*lambda*M/(4*delta)` lower bound. `relative_le_marked_expectation` and `marked_relative` preserve the literal source coefficient `xi/(8*C0)` relative to the sampled full mass. No individual marked-density lower bound is assumed.

`two_ends`, for `alpha<=1`, transfers all actual finite ball tests to every original physical ball of radius between `delta` and one. Its coefficient is exactly `(8*ballCoefficient n)*B`, independent of the actual alpha in that range. It uses the broad sampled lower density and the existing geometric all-ball covering theorem.

`closed_broadness` applies `SphereNetCapTests.sampled_closed_broadness` to the same outcome, then identifies its rows with the actual unlabelled marks. It proves the coefficient `1/10` for closed theta-caps at every original grid label and every unit direction. Labels outside the finite support have an empty marked row. No original-direction test mask is silently substituted for the net mask. Open-cap `broadness` follows by inclusion and likewise quantifies unit centers, as required by the source.

## Remaining assembly and provenance

The root-owned joint probability proof must now construct this exact `omega/good` on the same raw law, using the two separate one-eighth failure bounds and the actual high-mass alternative. It can then call `of_sample` and the proved output methods without supplying a narrow-band condition or another geometric oracle.

Audit record: `sphere_net_sample_realization_audit.json`; exact-source log: `SphereNetSampleRealization_axioms.log`. No frozen source, shared registry, verifier, lakefile or published output package was changed. The separate read-only review of the source density/ball probability wrapper is `sampling_source_geometric_failure_geometry_review.md`.
