# Section 7: actual coarse angular-scale pieces

`LocalAngularCoarse.lean` is clean-built and stable. It contains ten named theorems and one definition. The full source, followed by the production all-local-declaration audit, compiled without warnings, errors, or tactic diagnostics. All twelve local environment entries, including eleven theorem entries, depend only on `propext`, `Classical.choice`, and `Quot.sound`.

Source SHA-256: `616d175444049e9289c05672e47e4282e17670e5ad687cbbadc047a7c40d7f90`.

The mathematical comparison is to Section 7 case 1 of the combined PDF: at `Nnew ≤ Nold^(1/(2n))`, one old shading contains at least a constant times `λ Nold` cells, while the desired right side is bounded by a constant times `Nold^(1/2) λ`. The module also covers normalized meshes above any fixed small-scale threshold.

## Actual cap population

For a real cap exponent `m ≥ 0`, define

`Kpop = packingConstant k * (max 1 angular)^m`

in actual ambient dimension `n = k+1`. This coefficient is proved strictly positive and depends only on fixed dimension, angular width, and cap exponent.

`local_cap_population` takes an actual `TubeFamily (k+1) M`, a unit vector `u`, the original `CapBound δ m A`, and the literal local direction condition

`projectiveDistance (F.tube i).direction u ≤ angular*tau`

for every indexed tube. Under `0 < δ ≤ tau ≤ 1`, it proves

`M ≤ Kpop * A * (δ/tau)^(-m)`.

The proof does not assume a total-population estimate. Set `a = max 1 angular`. If `a*tau ≤ 1`, the entire family is inside the actual cap of radius `a*tau`, and the original cap condition applies since `δ ≤ a*tau`. If `a*tau > 1`, the existing finite radius-one projective cover proves the total count, and `1 ≤ a*tau` transfers it to the normalized mesh. The large-radius case is therefore covered without applying the original cap hypothesis outside its allowed radius range.

## Real scale powers and density normalization

`coarse_power` proves

`deltaNew^(-D+eps) ≤ δ^(-1/2)`

from `deltaNew ≥ δ^(1/(2n))`, `n > 0`, `D ≤ n`, `eps ≥ 0`, and `deltaNew ≤ 1`. `coarse_power_old_shade` weakens this to `1/δ` when `δ ≤ 1`. The ambient quantity in the public theorem is explicitly coerced to the reals: its cutoff is `δ^(1/(2*((k:ℝ)+1)))`. It is a real exponent, never natural-number division.

The actual finite selected shading density may be as large as two. Accordingly, the module permits a fixed `lamMax > 0` and assumes only `0 < lam ≤ lamMax`. The theorem `bounded_density_power` proves

`lamMax^(1−C) * lam^C ≤ lam`

for `C ≥ 1`. This retains the exact fixed normalization cost rather than assuming that the finite density is at most one.

## Final actual-family bounds

`coarse_family_bound` takes actual old finite shadings with `F.Comparable δ lam`, an old cell set `S` containing each `F.shade i`, the actual cap and local direction hypotheses above, and

`D < m+1 ≤ k+1`, `C ≥ 1`, `eps ≥ 0`, `δ^(1/(2(k+1))) ≤ δ/tau`.

It proves

`[lamMax^(1−C)/Kpop] A⁻¹ (δ/tau)^(m−D+eps) lam^C M ≤ #S`.

The displayed coefficient is explicitly fixed before `δ`, `tau`, `lam`, `M`, `A`, and the actual family and cell set vary. The proof derives the cap population internally and, for a nonempty family, chooses an actual index whose old shading has at least `lam/δ` cells. Its inclusion in `S` gives the final old-cell lower bound. Empty families are handled directly. No desired union-count bound, cap-population oracle, sampling outcome, marked-pivot theorem, or analytic estimate is a premise.

Admissibility, direction separation, and bounded tube bases are not required by this counting argument: the full cap condition and the actual old-shading lower density suffice. Thus the theorem applies to the actual admissible families without unnecessarily strengthening their geometric assumptions.

`bounded_scale_family_bound` replaces the power cutoff by any fixed `a > 0` with `a ≤ δ/tau`. Its coefficient is

`lamMax^(1−C) / [Kpop * max(1, a^(-D+eps))]`.

It handles the normalized-scale range above a sampling threshold chosen uniformly beforehand. This result needs no relation between `D` and the ambient dimension and no sign restriction on `eps`; the fixed maximum bounds the actual scale power.

For the finite adapter `AngularSpatialSampling`, the intended instantiation is its actual `boxFamily`, old set `SpatialGridPopulation.refinedCells`, `box_comparable`, and the cap/local-radius-three fields of `box_geometry`. Set `lam = V.density`, `lamMax = 2`, and `angular = 3`. The physical normalized density is at most this finite density, so its target follows by monotonicity of the nonnegative density power. The module itself does not assert that identity or replace the actual finite family by a different one.

## Complementary logarithms and remaining scope

`complementary_log_comparison` proves

`log(2/δ) ≤ 2(k+1) log(2/deltaNew)`

under the complementary real-power cutoff `deltaNew ≤ δ^(1/(2(k+1)))`. `not_coarse_log_comparison` provides the direct version for the negation of the coarse branch at `deltaNew = δ/tau`. Both include the additive `log 2` used in the formal conditioning budgets.

This module closes the individual coarse and bounded-normalized-scale piece bounds. It does not construct the common angular/spatial decomposition, select or sum its good pieces, discharge the sparse-density hairbrush case, or assemble an unrestricted estimate. Those separate operations remain outside the proved statements.

No shared/frozen source, common Lake file, verifier, registry, or published snapshot was edited.

## Verification artifacts

Commands in the matching development Lean project:

```sh
lake env lean -o .lake/build/lib/lean/LocalAngularCoarse.olean LocalAngularCoarse.lean
lake env lean ../local_angular_coarse_axioms.lean
```

The generated audit source and actual Lean output are `audit_work/local_angular_coarse_axioms.lean` and `audit_work/local_angular_coarse_axioms.log`. `audit_work/local_angular_coarse_audit.json` records the checked source hash, complete local-declaration inventory, and axiom set. Checks covered the exact source prefix, every named theorem's audited presence, no forbidden constructs or diagnostics, standard-only axiom closure, and a fresh compiled `.olean`.
