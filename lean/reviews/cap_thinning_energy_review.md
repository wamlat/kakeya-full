# Independent review: cap-preserving thinning and measurable energy

Reviewed `CapThinningGeometry.lean`, especially `full_cap_thinning` and its geometric/rounding dependencies, and the complete current `MeasurableEnergy.lean`. No incorrect statement, missing positivity premise, circular selection assumption, or measure-finiteness flaw was found.

## CapThinningGeometry

The rounding hierarchy is constructed from the actual finite occupied label fibers. Its supports, disjointness, proportional fractional feasibility, and occurrence of every block are proved. Integer ceilings are computed from original populations, and the reciprocal selection factor is used only after proving that denominator is at least one. Negative integer labels are handled by integer floor/division identities; no positive-coordinate restriction is silently imposed.

The geometry of the positive chart is used in both necessary ways: it controls within-cell chord distance from the other coordinates, and it prevents two selected vectors from being almost antipodal. The modular coloring therefore proves genuine projective separation, not merely separation of signed representatives. Three-color residues cost exactly a fixed factor 3^k.

Original populations in large chart cells use the finite radius-one cap cover. Smaller cells use the input cap bound only at radii between δ and one. The hypothesis m≥0 is explicit wherever power monotonicity and the ceiling comparison require it. Arbitrary projective caps are covered by two actual projected lattice boxes, and dyadic rounding is upward, so the cap itself is covered. Ceiling losses are bounded using 2^(jm)≥1.

`full_cap_thinning` has the correct quantifiers and retention normalization. Constants depend only on k,m; a single inverse input A and the factor (r/δ)^(-m) remain. The selected original indices have separation 2r/(k+1), and all caps at radii r≤u≤1 satisfy the claimed uniform m-growth. Original direction separation is not assumed. The signed chart family is only an auxiliary direction representation; the final separation and cap conclusions concern the original tube directions. Its temporary zero bases and empty shadings are not used as a geometric conclusion.

This is an actual finite direction-selection theorem. Building a reindexed TubeFamily and transporting spatial shadings through later translations or dilations remains the responsibility of an application theorem. Those spatial conclusions are not asserted by `full_cap_thinning` itself.

## MeasurableEnergy

`finite_shading_energy` proves Cauchy–Schwarz for the actual multiplicity function, its actual support union, and the exact double sum of measured intersections. Indicator L2 membership and all required finite-measure/integrability statements are derived from measurable finite-measure shadings. The ambient measure need not be finite or σ-finite.

The standalone `indicator_integral` identity permits infinite-measure sets because both the nonintegrable Bochner integral convention and Measure.real at infinity evaluate to zero. This does not undermine the energy applications: every shading, intersection, and finite union used there is explicitly proved finite before the identity is applied.

`finite_shading_union_lower` cancels the positive index count only in the nonempty case and handles the empty type separately. Its positive row-bound premise is explicit. `tube_shading_energy` inserts the proved actual two-tube intersection bound with denominator max(projective chord distance,δ), correctly covering parallel directions and diagonal pairs.

`finite_union_overlap` derives the bounded-overlap volume inequality by integrating the actual pointwise multiplicity bound. It does not assume that volume inequality as an input. Even though K≥0 is not listed separately, the pointwise hypothesis supplies it whenever the space is nonempty; the empty-space conclusion is harmless.

These energy results do not alone prove the fractional/Wolff seed: the required summation of pairwise geometric overlaps against the cap distribution remains a separate analytic step. No such seed is incorrectly claimed in the reviewed file.
