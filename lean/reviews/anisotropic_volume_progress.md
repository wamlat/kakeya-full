# Exact anisotropic volume normalization

AnisotropicVolume.lean is compiled and verified. It bundles the actual transverse stretch as a linear map, proves it equals the explicit diagonal matrix with eigenvalues1,tau⁻¹,...,tau⁻¹, and computes its determinant as tau⁻k in ambient dimension k+1.

The actual normalization map includes the original orthogonal frame and common spatial translation. It is a genuine homeomorphism with the previously explicit inverse, so measurable images remain measurable. For every set Y and tau>0, including outer-measure statements without a measurability premise,

volume(normalizeBox u tau q '' Y) = ofReal(tau⁻k) * volume(Y).

Real volume has the corresponding exact identity /tau^k. Finite measure remains finite. An arbitrary indexed union has exactly the same factor because one map is shared by the entire group. Orthogonal framing and translation are proved measure preserving; these are not hidden assumptions on the input sets.

This verifies volume normalization independently of the direction cap/count and actual-grid interfaces. It does not assume that images of rotated cells form an aligned grid.

Verification uses Lean4.33.1 and Mathlib commit0df444a360eaa60ab8c11dca51a86af692955474. From audit_work/formalization:

```
/Users/ssoh/.elan/bin/lake env lean -o .lake/build/lib/lean/AnisotropicVolume.olean AnisotropicVolume.lean
/Users/ssoh/.elan/bin/lake env lean ../anisotropic_volume_axioms.lean > ../anisotropic_volume_axioms.log
```

Clean compilation, no warnings. All12 theorem declarations are audited by printing axiom dependencies from a full copy of the source; all lists are subsets of `{propext, Classical.choice, Quot.sound}`. No sorry or custom axioms.
