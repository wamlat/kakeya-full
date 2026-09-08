# Whole-sphere angular sampling tests

`SphereNetCapTests.lean` is clean-built and frozen outside the 381-module checkpoint 21. Its exact-source audit passes with 9 named theorems, 15 local theorems and 16 all-local declarations, using only standard Lean foundations. The source SHA is `1a904c253c381ecbf814760a7cad0409c304628d4f3368eb006fafbda8cc06a2`. The machine audit record and log are `sphere_net_cap_tests_audit.json` and `SphereNetCapTests_axioms.log`.

## Concrete geometric and sampled interfaces

Given the actually constructed `N : ProjectiveSphereNet.Net k theta` and original `F : TubeFamily (k+1) M`, the Boolean test family is

    cap N F : Fin N.points.card → Fin M → Bool
    cap N F a i = decide (projectiveDistance (N.center a) (F.tube i).direction < 2*theta).

Thus the number of angular tests is exactly the cardinality of the whole-sphere net, independently of the number of original tubes. `cap_containment` proves every closed original theta-cap is contained in one of these open doubled tests on any original finite row. It includes empty rows and centers absent from all original tube directions. `all_closed_caps` transfers any uniform numerical bound on these tests to every original unit cap center.

`row_cap_card` identifies the literal cardinality of each tested sampled marked row with `markedCapCount` for these same masks. `sampled_closed_broadness` then proves all-cell, all-unit-center closed-theta marked broadness with coefficient 1/10 for an actual outcome satisfying `SampleGood` for this test family. It keeps the original outcome and marks; outside the high support the actual marked row is empty. This is a conditional geometric transfer, not an assertion that a good outcome already exists for the new test family.

## Actual raw expected means

`cap_mean_le` integrates actual almost-everywhere marked incidence bounds over each original grid cell using the proved finite-cell measure identities. `cap_mean_from_bounded_radii` applies the original a.e. broadness only at the tested radius `2*theta`, requiring exactly `delta <= 2*theta <= 1`. All net centers are actually unit, and the open net cap is a subset of the original closed cap. Its coefficient is exactly `K*(2*theta)^beta`, with no density ratio or normalization loss.

`capMean_admissible` derives the finite sampling premise `1000*capMean <= markedMean` from this geometric mean estimate and the explicit scalar cap budget. `source_cap_test` discharges that scalar budget at the original `theta = SamplingTheta.choice K beta`. It works for **any finite set of original grid labels**, with raw probabilities `weights G delta S`; no unit-axis carrier, support-cardinality, mean, ball, or probability bound is assumed. This interface can therefore use the source's actual variable-length support unchanged. `input_cap_test` also instantiates the existing original `SamplingNormalizedMeans.Input` and its exact `rawMarked` support directly.

The measurable sets need only be measurable for these cap means. Their cell intersections are finite because the grid cells are finite; no unsupported global finite-measure hypothesis is hidden. The only pointwise analytic input is the source's a.e. marked broadness. No new axiom was added.

## Remaining source display boundary

Together with `ProjectiveSphereNet`, this constructs the literal full-sphere test masks and their actual expected angular means. The numerical inverse-theta net-cardinality budget is handled separately by `SphereNetBudget`. The source's full (6.19) probability display still requires applying the real finite-product tail/event lemmas to these **new masks**, summing their actual high-cell test count, proving the individual `<1/8` bounds and the combined `>3/4` success probability, and carrying that same outcome into the source realization. The old original-direction test family must not be silently relabeled as this smaller family.

No frozen source, shared registry, verifier, lakefile or published output package was changed.
