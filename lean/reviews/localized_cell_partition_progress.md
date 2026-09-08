# Actual old-cell spatial partition for Section 8

`LocalizedCellPartition.lean` is frozen, compiled, and audited. It does not use an external axiom or assume a desired spatial partition.

For an actual finite tube family whose old δ-cell centers lie in individual radius-ρ balls, label each old cell by its centered ρ-grid cell. The number of occupied labels within one localization ball is at most

`K(n) = (2 ceil(1+n/2)+3)^n`.

This is derived from the proved grid-ball count, including the coarse cell-center offset. No integrality relation between δ and ρ is imposed.

`construct` chooses a genuinely largest occupied bin on every tube. It then invokes the proved minimum-cardinality trimming construction on those actual bins, retaining every original tube index. For original factor-two comparable density s>0 and M>0, the output `Partition` has a common positive integer row cardinality N, retained density ν=δN, and:

- s/K(n) ≤ ν ≤ 2s;
- each retained old shade is a subset of its original shade;
- every retained cell on tube i has one global label assignment(i);
- every original shade has at most 2K(n) times its retained cardinality.

Consequently the original relative ball tests pass to retained shadings with coefficient 2K(n)B. Trimming is actual finite subset construction, not an assumed rounding or comparability output.

The compressed `Partition.groupFamily` keeps the original axes and selected old labels. Its direction cap and separation conditions inherit from the original family. `population_sum` proves that the group populations sum exactly to M. `union_sum` proves that the sum of old group-union cardinalities is bounded by the original union cardinality: different groups are disjoint because their old cells have distinct global labels.

For group q, the common physical origin is the center of the old fine-grid label nearest the ρ-grid center q. Any original localization center represented in that group is within (1+n)ρ of this origin. `normalized_group` constructs real unit axes at scale δ/(8Wρ), W=max(1,width), with base norm at most (6W+1+n)/(8W). It preserves each actual retained shading cardinality and the exact group union cardinality by an injective integer-label shift. This explicitly closes the common-origin/bounded-base issue that the seed-only normalization did not need to address.

## Scope and next interface

This module proves actual finite partitioning, proportional retention, direction inheritance, relative two ends, and common-origin bounded rescaling. Its 8Wρ rescaling alone does not claim normalized density≤1. A separate `LocalizedGroupedNormalization` module is in progress to use the existing larger `dilationConstant`, derive legal density from actual local tube counting, and perform actual direction thinning. Applying a two-ends estimate and summing the resulting analytic bounds remains downstream.

## Verification

Commands run in the development Lean project:

```
lake env lean -o .lake/build/lib/lean/LocalizedCellPartition.olean LocalizedCellPartition.lean
lake env lean ../localized_cell_partition_axioms.lean
```

The audit copy contains the exact full source followed by the production environment axiom collector. It audits all local declarations, including definitions and structure-generated declarations. Both compilation and audit produced zero warnings/errors. Source scan excludes sorry, admit, custom axiom declarations, unsafe, and native_decide.

- 24 named source theorems, 10 definitions, one structure.
- 69 local environment declarations, including 44 theorem declarations.
- Axiom union: `propext`, `Classical.choice`, `Quot.sound` only.
- Source SHA256: `6868d9372707681e6320130a647660569c6f5a160543d1373a6f7866084ed0a2`.
- Lean 4.33.1; mathlib commit `0df444a360eaa60ab8c11dca51a86af692955474`.

Machine-readable evidence: `localized_cell_partition_audit.json`; full audit copy/log: `localized_cell_partition_axioms.lean` and `.log`.
