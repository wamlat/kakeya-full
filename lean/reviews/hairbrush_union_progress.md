# Actual hairbrush plane-bin union assembly

`HairbrushUnion.lean` has 8 theorems and 2 definitions. Its final theorem constructs a finite maximal projectively δ-separated net of actual transverse bristle directions, assigns every original bristle, proves pointwise plank overlap ≤ C_d s^{-(d−2)}, integrates that overlap, proves each actual bin union lower bound using `PlanarEnergy`, and sums the original bristle cardinality exactly. The result is

`#H λ² δ^(d−1) s^(d−2) / (C(d,R) L³) ≤ volume(⋃ Y_T)`.

All quantities are actual finite tube data and Lebesgue measures. No net existence, packing inequality, pointwise overlap estimate, energy inequality or support cardinality is assumed. Inputs still state actual incidence with one stem, direction separation, positive angle from stem, source shading measurability/containment/mass, bounded location and stem-axis distance. `HairbrushRemoval` derives the latter geometric/shading inputs from actual crossing-ball removal.

Compilation is clean with Lean 4.33.1 and the pinned mathlib. No `sorry`, custom axioms or opaque geometric assumptions occur.
