# Actual anisotropic carrier normalization

`AnisotropicRescaling.lean` is a verified extension of the angular/spatial finite assignment. It uses the actual orthogonal `alignStem` frame and the actual affine `SpatialAngular.normalizeBox` map. No rescaled carrier estimate is assumed.

Verified statements:

- Transverse dilation `stretch tau` fixes one coordinate and multiplies the remaining k coordinates by `tau⁻¹`. `compress tau` is its actual two-sided inverse when tau≠0.
- For 0<tau≤1, every distance is enlarged by a factor between1 and1/tau. The same bounds hold for the actual framed and translated spatial-box map.
- An original unit direction in the projective cap of radius angular*tau about a unit stem has actual transformed speed between1 and1+angular. Thus its transformed axis has uniformly bounded length. The proof does not silently regard this segment as a unit segment.
- The transformed axis formula is exact. An original carrier of radius width*delta is covered after normalization by `ceil(1+angular)+1` explicit unit tubes of radius width*(delta/tau). Their bases are integer translates along the actual normalized transformed direction. For angular=3 the cover has five members. It is valid without any implicit direction orientation or original axis-parameter choice.

Remaining interface: direction cap and separation normalization, actual transformed-grid rounding/counts, and volume scaling are separate extensions. The current theorem does not claim these from the carrier cover. Repeated parallel unit segments need separate finite colors when direction separation is required.

Verification: Lean4.33.1; Mathlib commit0df444a360eaa60ab8c11dca51a86af692955474. From `audit_work/formalization`:

```
/Users/ssoh/.elan/bin/lake env lean -o .lake/build/lib/lean/AnisotropicRescaling.olean AnisotropicRescaling.lean
/Users/ssoh/.elan/bin/lake env lean ../anisotropic_rescaling_axioms.lean > ../anisotropic_rescaling_axioms.log
```

The source compiles without errors or warnings. The full-source axiom audit prints all20 theorem declarations; every dependency list is contained in `{propext, Classical.choice, Quot.sound}`. There are no `sorry` declarations or custom axioms.
