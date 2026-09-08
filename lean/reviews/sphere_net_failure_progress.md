# Literal high-cell and sphere-net probability budget

Two new sources, `SphereNetFailure.lean` and `SphereNetSourceFailure.lean`, prove the actual angular probability calculation in source (6.19). Both production `.olean` files compile with zero diagnostics, and both exact-source audits PASS using only standard foundations. The generic module has 4 named / 13 local theorems / 17 all-local declarations; the original-geometry module has 1 named / 4 local theorems / 6 all-local declarations. They are outside the already published and frozen 381-module checkpoint 21.

## Actual probability event

`SphereNetFailure.law p q hq hqp hp` is definitionally the existing `coupledLaw (flatten p) (flatten q) ...` on `Outcome T C`. Each tube-cell coordinate uses the original three states (absent, full-only, marked), with the actual nested probabilities. `DecidableEq T` and `DecidableEq C` are explicit so that the finite outcome type is the same one used by the other sampling modules.

The event `angularFailure q high cap omega` means that, at some actual high cell, either the sampled total marked count is at most half its expected marked count, or the sampled marked count in one actual doubled net cap is at least one twentieth of that same expected total. These non-strict bad thresholds slightly enlarge the source's strict bad events. Both types of failure are included; the event does not contain tube-density or tube-ball failures.

`probability_le` proves

    Pr(angularFailure) <= #high * (1 + #Caps) * exp(-cut/8)

from the actual product-law Chernoff theorems, a lower bound `cut` for high-cell means and the factor-1000 cap mean condition. It applies a finite union bound to the exact index type `high × Option Caps`: `none` is the cell lower-tail test, and `some a` is the cap upper-tail test. The extra `1` is therefore present even when the cap family is empty. No independence between overlapping tests is assumed, and no failure probability is supplied as a hypothesis.

## Exact source count and exponential

`test_count_threshold` derives

    #high * (1 + #net) <= N^(ambient+2)

at a threshold fixed before the actual net, radius, population and high-cell set. Its inputs are only the fixed inverse-radius polylog budget and fixed spatial coefficient in `#high <= P*N^ambient`. The actual whole-sphere packing bound gives `#net <= H*N` after the proved logarithmic-power estimate. Both `P` and `1+H` are absorbed into the fixed threshold. Thus the final coefficient-one count is not obtained by dropping a spatial constant or forgetting the cell lower-tail tests.

`source_tail` proves the literal exponential display is less than `1/8` for `N>=16`, using exactly

    a0 = 64*(ambient+4).

The exponent after the proved logarithmic tail comparison is strictly negative with ample margin. The proof bounds it by `N^(-1) <= 1/16 < 1/8`; the actual paper coefficient is unchanged. `uniform_probability` combines this count and the actual finite-product probability bound.

## Original measurable geometry, without expectation or count oracles

`SphereNetSourceFailure.source_angular_failure` fixes ambient dimension, width, original base bound, upper axis length, broadness budget coefficient, broadness exponent and logarithmic power before choosing its positive mesh cutoff. All actual families, lengths, shadings, densities, marked fractions and conditioning constants occur after that cutoff.

For an actual `SamplingLengthInput.Input`, the theorem constructs:

- The original bounded-support raw probabilities, using exact cell intersections.
- The actual high set defined by the expected marked multiplicity and source `a0*log(2/delta)` threshold.
- A full-sphere net at the original `SamplingTheta.choice K beta`, with `delta <= 2*theta <= 1`.
- The coefficient-one count of all high-cell and net-cap tests.
- The actual raw-law angular failure probability bounded by the exact source exponential, and that exponential strictly below `1/8`.

The support cardinality is derived from actual bounded variable-length carriers and the original grid. Its full fixed geometric prefactor is retained until the threshold construction. The cap means are obtained by `SphereNetCapTests.source_cap_test` from the original a.e. measurable marked broadness; no mean, test count or good outcome is supplied. The original theta lower bound is inverted with its fixed coefficient and real logarithmic power, so no row-density-ratio change occurs. `rawLaw h` and `highCells` expose the exact arrays and event for subsequent combination with the density/ball proof.

No separation assumption or lower-density growth condition is needed for this angular part: the number of cap tests is controlled by the whole sphere net, and the high means themselves supply the tail cutoff. The stronger input structure retains the original source geometric and measurable hypotheses. Density/ball growth conditions remain relevant to the separate event analysis.

## Remaining joint-realization step

The source angular display (6.19) is now proved on the actual original raw probability model. This does not by itself prove that all source density, ball and angular events hold with probability greater than `3/4`. The remaining combination must use this same law and original data, combine the distinct density/ball failure probability with the angular bound, and transfer the actual common outcome to the source shadings and retained mass. Root owns that separate assembly. No `SampleGood` outcome is assumed or claimed here.

## Verification

`SphereNetFailure.lean` SHA: `3667726a67e39c9766916bc246bc5b4fde4d721892e53d8f074bfefc6d73735a`.

`SphereNetSourceFailure.lean` SHA: `36e453b75585065954290a11affb96e5d09db74f32afc638bbf0cc491043fc09`.

Machine dependency records and exact-source logs are `sphere_net_failure_audit.json`, `sphere_net_source_failure_audit.json`, `SphereNetFailure_axioms.log` and `SphereNetSourceFailure_axioms.log`. No frozen source, shared registry, verifier, lakefile or output package was edited. The independent review of the exact no-error bush length adapter is separately recorded in `bush_lengths_geometry_review.md`.
