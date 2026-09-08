# Actual general-operator L1 estimate

`KakeyaOperatorL1.lean` is frozen and clean-built. It imports the actual operator definition and the exact isometric tube-volume identity, and proves the L1 endpoint directly rather than assuming an operator inequality.

For every nonnegative ENNReal-valued f, every original base b and unit direction v, the integral over its actual carrier is at most the global input integral. Dividing by the exact common denominator and taking the supremum over ALL original bases proves `maximal_le_global`. Integrating this pointwise inequality over the actual sphere measure proves

`∫sphere maximal δ f ≤ coefficient k δ * ∫volume f`,

where ambient dimension is k+1 and `coefficient k δ = sphereMeasure(k+1)(univ)/referenceVolume k δ`. The coefficient is finite for δ>0. The proof works with infinite input mass and does not turn an infinite measure into a real number.

The actual tube-volume lower bound also gives

`ofReal(lowerVolumeConstant k * δ^k) ≤ referenceVolume k δ`,

with `lowerVolumeConstant k = unitBallVolume(k+1)/2^(k+2)>0`. Consequently `maximal_lintegral_scale_le` proves

`∫sphere maximal δ f ≤ scaleConstant k * (ofReal(δ^k))⁻¹ * ∫volume f`,

where `scaleConstant k = sphereMeasure(k+1)(univ)/ofReal(lowerVolumeConstant k)` is finite and depends only on dimension. This is the literal δ^{-(n−1)} L1 loss, valid for every δ>0. Inverting the product in this derivation uses the proved positivity and finiteness conditions, avoiding ENNReal's zero-times-infinity exception. `normMaximal_lintegral_le` specializes to the actual real-function operator through ofReal(abs f).

These ENNReal integral inequalities need no measurable-input assumption: set-integral monotonicity, pointwise supremum and integral monotonicity are valid as stated. For a nonmeasurable integrand, Mathlib’s lintegral is the lower integral, so no outer-integral claim is made. These lemmas do not themselves establish measurability of the maximal function. The separate parameter-integral/semicontinuity construction supplies that fact for measurable inputs before invoking norm-space interpolation.

Verification: clean compilation with zero diagnostics; production exact full-source audit of 16 local declarations, including 13 theorem declarations, with ten named source theorems and three definitions. Only `propext`, `Classical.choice`, and `Quot.sound` occur. Evidence: `KakeyaOperatorL1SourceAudit.lean`, `KakeyaOperatorL1_axioms.log`, and `KakeyaOperatorL1_audit.json`.

Frozen SHA-256: `6165bffc59ed8c9df0bc53653fa857ec3467f75a70fed73148d29a7b749aa542`. No frozen module or registry was edited.
