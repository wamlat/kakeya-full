# Separate review of LegalSampleNormalization

Reviewed the frozen source on 6 September 2026. No mathematical defect or hidden strengthening was found in its five theorem statements and two proof-bearing definitions.

The normalization is genuinely common: every spatial point is multiplied by `R⁻¹`, every grid scale becomes `δ/R`, and the first direction is reversed using one sign in `{1,−1}`. The raw intermediate and first-endpoint scalar coordinates are both multiplied by that sign and divided by R; the second scalar coordinate is divided by R. Thus the physical projected points are exactly the common homothetic images, including the negative-orientation case.

`normalizeAngle` correctly weakens the directional lower bound from κ to `κ/R` when `R≥1`, preserves unit directions, and derives the lower intermediate coordinate by division by positive R. `normalizeEndpoints` derives the normalized gap, first-coordinate upper bound, and both absolute second-coordinate bounds. All required raw bounds are explicit inputs; legal abundance is not smuggled into these definitions.

`normalized_cell` preserves original integer labels under the common homothety, and `normalized_center_distance` scales actual geometric errors by precisely `1/R`. `normalized_pivot_exact` verifies that the ratio a/b is unchanged by both common scaling and common first-axis reversal; it then proves exact equality of the intermediate point and pivot with their homothetic originals. The sign reversal does not alter the perpendicular projection (`transverse_signed`).

The module is an adapter for each actual raw legal sample. It does not yet assemble all raw triples into one finite indexed collection, prove the transverse-angle count, build transformed unit tube families, or establish every rounding-map equality. Those are separate remaining interfaces. In particular, the old unit segment becomes a segment of length `1/R`; this file does not claim that it remains a unit tube. Its actual `Angle`/`Endpoints` and grid/error conclusions are sufficient in scope and contain no false unit-length assertion.

Together with `LegalTubeSamples`, taking the fixed `R=1+2·width` matches the raw coordinate bounds. Then `δ≤κ` implies `δ/R≤κ/R`, and the label map remains injective because the labels themselves are unchanged. The orientation and scaling costs are fixed geometric constants, not hidden density losses.
