# Actual joint-segment geometry and fixed coloring

`AnisotropicJointGeometry.lean` is frozen and clean-built. It contains 17 theorems and 4 definitions. It uses the actual marked-best segment choices and the actual measured original-index restrictions; no substitute directions or duplicated segment indices are introduced.

## Direction and base constants

In ambient dimension `k+1`, write `delta'=delta/tau`, angular width `a`, and

- `sigma=1/[4(1+2a)^2]`;
- `Ccap=packingConstant(k)*[8(1+2a)^2]^m`;
- `Rbase=1+|R|+|W|+segmentCount(a)`.

The actual joint segment family is `sigma*delta'` separated when the original family is delta-separated. An original real-m cap bound with coefficient A becomes the actual delta'-scale cap bound with coefficient `Ccap*A`. These facts are proved using the actual selected segment axes and inherit unchanged through the measured original-index restriction.

The fixed base bound explicitly requires actual original bases in the **same** genuine spatial box:

`(F.tube i).base ∈ SpatialAngular.parallelBox u tau q R W`.

For the measured-family theorem this is required only for retained indices. The box label q is common to every such index and is the literal label used by `normalizeBox`. An angular cap alone is not treated as a spatial box. The proof uses the already-proved `normalizeBox_width`/selected-base interface and the actual bound on the marked-maximizing segment index.

## Complete color partition

`measured_coloring` constructs a full coloring of the actual measured family. Every color family is exactly delta'-separated and inherits the actual cap/base bounds. Every arbitrary real tube weight is counted exactly once across all reindexed classes. The explicit palette bound is

`P ≤ packingConstant(k)*[4(1+2a)^2]^k+2`.

There is no delta, tau, population, density, or A dependence in this palette.

## One-color preparation for the sampling interface

`joint_colored_selection` constructs an actual color using the marked mass of the marked-best segment outputs. It retains at least `1/P` of their total marked mass. Both the full output Y and marked output O are restricted to that SAME color, with all original tube indices still available as the ambient indexing type.

The positive-full-mass implication is proved: every original index with positive mass in this color-restricted full set must have the selected color. Consequently, any actual subsequent positive full-density class has exact delta' separation. Its real-cap and base bounds are derived from the original actual geometry.

This is staged deliberately before `MeasurableMarkedSelection.select`: use the color-restricted Y and O there while retaining **all** exact image-G reference rows. Its actual positive full-density conclusion then discharges the color premise and its proportional marked filter restores broadness. No statement here asserts that selecting a color after broadness recovery preserves broadness. The frozen uncolored `AnisotropicJointRecovery.construct` cannot simply be color-thinned while reusing its marked broadness unchanged.

The helper theorems prove color-restricted nestedness, measurability, literal subset relations, exact color-fiber mass identity, and actual marked-mass color selection. These provide the geometry/mass interfaces needed to compose the colored measured recovery with `SamplingMeasurableAssembly`.

## Remaining explicit boundary

The actual common spatial-box decomposition is outside this module. A whole angular group may occupy many such boxes. The future assembly must construct the groups with the stated common q/R/W property from existing spatial decomposition interfaces and sum them with the appropriate mass/overlap accounting.

The module also does not reprove the full colored measurable recovery or logarithmic budget algebra. It provides the actual color choice and proves the separation/cap/base conclusions for the positive full-density class that the existing measured recovery constructs. Original measurable full/marked mass, physical two ends, broadness and their parameter budgets remain the responsibility of the preceding actual input construction.

## Validation

Clean original source compile and `.olean` build. Exact full-source audit appends all 21 named declaration axiom reports to the unchanged source. No custom axiom, placeholder, assumed coloring, or geometric cap-count oracle is introduced. All 21 audits passed. The only foundations used are `propext`, `Classical.choice`, and `Quot.sound`.

Source SHA-256: `ee5f7d782732f013559fa2a4aa1ca3c9b12be647096d0b98cdd0c78029896830`.
