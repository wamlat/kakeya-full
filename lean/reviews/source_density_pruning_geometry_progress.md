# Source Section 3.3 pruning geometry

`SourceDensityPruningGeometry.lean` is frozen, clean-compiled, and exact-source audited. SHA256: `4d184d94334bf531dc00b3d12aaf352ad6a9a1418fd6bb2b7ae97b9e769ef2c4`.

The module proves 18 named source theorems. The production audit traversed 27 local theorem declarations and 30 total local declarations, including proof-bearing definitions; every dependency is in the standard foundational set `propext`, `Classical.choice`, `Quot.sound`. There are no custom axioms, `sorry`, `admit`, or `native_decide`, and compilation/audit emitted no warnings or errors. Audit details: `source_density_pruning_geometry_audit.json`; raw exact-source transcript: `SourceDensityPruningGeometry_SourceAudit.log`.

The definitions `survivingPiece`, `markedPiece`, and `kept` use the exact original `SourceDensityPruning` masks, original tube indices, and one-piece assignment. They make no new selection. The full surviving row is the original Y_i or empty; its good-set intersection is a separate marked shading. `surviving_piece_nonempty` recovers the actual assignment and survival certificate from any nonempty output row.

The density theorem gives a*lower <= measure(surviving row) <= upper from the actual reference density bounds, original containment Y_i subset Full_i, and finite full measure. `active_density` exposes this on every actual nonempty output row without a supplied selection predicate. For every original test radius delta <= r <= 1, `all_rows_two_ends` gives coefficient B/a on the full surviving rows, including deleted or unassigned empty rows. It uses only a>0, delta>=0, B>=0, finite full sets, actual containment and the original full ball inequalities. The relative good-set restriction is not substituted for those full rows.

`surviving_broad_on_good` uses the exact good-set inequality old multiplicity <= 2*surviving multiplicity. `goodRows_broad` and `marked_piece_broad` derive coefficient exactly 2*K for the actual marked rows, at all original radii in the existing Broad predicate. Outside the good set the marked incidence row is empty. The original piece broadness is the geometric input; broadness is not assumed for survivors or marks.

`retained_half_mass` is the literal threshold condition on the actually retained piece labels. `retained_overlap` and `retained_marked_overlap` inject each actual occupied retained label into the corresponding original occupied piece label, so all pre-existing pointwise overlap bounds are preserved. Measurability and finiteness of both full survivors and separate marks are derived from the original measurable finite shadings.

This module closes the geometric implications (3.6)-(3.8) and preservation of overlap on the actual masks used by the parent's mass theorem. The exact deletion, 3W/4 good-mass and 5W/8 retained-mass conclusions remain proved in `SourceDensityPruning.source_fractions`, on the same definitions. The companion does not construct the upstream angular/spatial pieces; their actual original broadness and overlap are supplied by those already proved refinements. No final angular, mass, or two-ends conclusion is hidden in a new output record.

Commands, run in `audit_work/formalization` with the pinned Lean/mathlib environment:

```sh
lake env lean -o .lake/build/lib/lean/SourceDensityPruningGeometry.olean SourceDensityPruningGeometry.lean
python3 ../audit_source_density_pruning_geometry.py
```

The audit script copies the exact complete source, appends the production verifier's all-declaration audit, compiles the copy, checks every reported axiom dependency, and verifies that every named source theorem appears in the audit. This is an individual source checkpoint; integrated publication remains the parent's responsibility. The read-only review of the two imported mass modules is recorded separately in `source_density_pruning_scalar_review.md`.
