# Actual anisotropic grid rounding: verified count interface and limits

AnisotropicGrid.lean compiles. It constructs the new label by applying the actual anisotropic affine map to each old delta-grid center and taking the unique half-open grid label at scale eta=delta/tau. No alignment between the rotated old grid and the new grid is assumed.

For ambient dimension k+1 and0<tau≤1, the actual rounding error is at most (k+1)*eta/2. If a finite old cell set S maps to one new label, the exact anisotropic image of its entire old cell union lies inside a Euclidean ball of radius(k+1)*eta. Exact old-cell volumes and the verified determinant factor tau⁻k then give

|S| ≤ C(k)/tau,
C(k)=(k+1)^(k+1)*volume(unit ball in ambient dimension k+1)>0.

The occupied new-label count is therefore at least tau*|S|/C(k). Rounded admissible tube centers belong to the explicit finite unit-tube cover with the fixed width enlargement width+(k+1)/2.

Scope limitation: this proves actual center rounding, carrier admissibility, fiber counts and occupied-label cardinality. It does not prove that the union of whole new isotropic cells has volume uniformly bounded by the exact anisotropic image of the old shading union. A transformed old cell has longitudinal thickness delta, while a new cell has thickness delta/tau. Claiming such a volume comparison would introduce a missing factor. The main normalization route consequently keeps exact measurable images and chooses one measurable unit-carrier intersection per original tube, as formalized separately in AnisotropicShading. No full-new-cell union comparison is used.

Lean4.33.1, Mathlib commit0df444a360eaa60ab8c11dca51a86af692955474. Compile from audit_work/formalization with `lake env lean -o .lake/build/lib/lean/AnisotropicGrid.olean AnisotropicGrid.lean`. Full-source audit source/log are audit_work/anisotropic_grid_axioms.{lean,log}; seven theorem declarations are checked. No sorry or custom axioms.
