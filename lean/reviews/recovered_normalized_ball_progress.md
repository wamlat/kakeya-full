# Recovered-family spatial bound at the normalized mesh

`RecoveredNormalizedBall.lean` composes the actual recovered-family union inclusion with the original spatial pruning's all-radius extension and common-homothety transport. It derives the exact normalized spatial bound required by the actual selected graph families, for the recovered family's full union at delta/(1+2width).

The input is the actual RecoveredInput record with O literally equal to PrunedIncidence.family F E delta L d J. The original small-radius pruning bound, original F admissibility and original bounded bases supply all large radii. The recovered union is literally a subset of O.unionCells, so every normalized ball-cell count decreases under the same cell-label inclusion. No original tube is presumed admissible at the smaller mesh.

The coefficient is spatialConstant(n,width,baseRadius,d)*L. The exact subsequent graph cap coefficient is also proved at least one when d≥0 and L≥1. Thus the selected graph construction can use this coefficient directly in the normalized discrete estimate.

Both source theorems clean-build and pass a full-source audit with only propext, Classical.choice and Quot.sound, without diagnostics. This module is later development than checkpoint11 and awaits the next full-package checkpoint.

Local theorem declarations audited: 2. Source SHA-256: `3b0effa641b6e5faf4807c3b8b4359fe063d29fc83e771da5dec03c9d9d4b8f3`.
