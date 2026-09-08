# Actual measurable angular construction and hairbrush summation

All four modules below are frozen, clean compiled, and exact-source audited using only the standard foundational axioms. There are no custom axioms, `sorry`, or Lean diagnostic warnings. This chain imports the separately audited exact measurable atom construction and actual weighted angular selection.

| Module | Source theorems | Source definitions/records | Environment declarations/theorems | SHA-256 |
|---|---:|---:|---:|---|
| MeasurableAngularGroups | 17 | 4 | 24/20 | `95ed3b2e288a04bb44adc6e9037e3834636fb82184df598c2cd484c9e1e14ae0` |
| MeasurableAngularPruning | 7 | 2 | 10/8 | `b5f191df07fe12b29caf9e29b2dbe38b839f1ea3be3e2280fc356152f1d1fbc1` |
| MeasurableAngularPieces | 2 | 1 | 37/20 | `4cd58e215019596dbc061c8fed1056d23a75afd8d35ac0522ff55474abfe8e4f` |
| MeasurableAngularHairbrush | 5 | 3 | 14/11 | `b4c3e82ccf8601182da6595af0afcfa0b8bc0cff85a2202c5dffcc83d44b4560` |

`MeasurableAngularGroups` constructs the nonempty original index set for an actual Set-valued group and compresses it injectively. Retained shadings have exactly the same union, incidence cardinalities, and mass after compression; full shadings use the same original indices. Direction separation, real cap bounds, and literal pointwise broadness are inherited. Unique assignment proves that the total active tube population across groups is at most the original population.

`MeasurableAngularPruning` deletes actual groups whose measured mass is below `(rate/4)*lambdaAbs*activeCount`. It proves that at least `3*rate/4` of the original absolute-density mass budget remains, and at least `3*rate/8` of the original tube population remains across retained groups. No per-tube lower mass of the selected group shadings is assumed. The full upper mass is paid using the unchanged original full shading on each active index.

`MeasurableAngularPieces.exists_pieces` now constructs actual measurable angular shadings from arbitrary measurable finite-volume original shadings. It applies weighted angular selection to exact incidence-pattern atom measures and then realizes every selected row as a finite union of the same atoms. Each new shading stays inside its own original shading. The common scale/depth, unique tube assignment, actual cap localization, measured retained mass, pointwise broadness, and pointwise group-union overlap are all constructed. The Piece record is not an analytic premise in this existence theorem.

`MeasurableAngularHairbrush` applies the existing actual measurable single-group hairbrush theorem to each retained compressed family. Full sets are unchanged original full sets on those indices. Summation uses actual measured group unions and the proved pointwise overlap bound; no grid union or artificial support is substituted.

For ambient `n=k+2`, actual unit radius-delta tubes, delta-separated directions, real cap coefficient `A>=1`, original full mass interval `[lambda*delta^(n-1),2*lambda*delta^(n-1)]` with `0<lambda<=1`, and actual full two-ends coefficient `B>=1` at every physical ball scale `delta<=r<=1`, the theorem `measurable_seed_at_depth` gives

`[seedConstant(k,J,alpha,beta,B,m,A)*3*retentionRate(k+1,J)/16] * lambda^2*M*delta^((m-3)/2) / hairbrushLog(k,delta/tau)^(5/2) <= volume.real(originalUnion)/delta^n`.

Here `alpha,beta>0`, `beta<=(m-1)/2`, and `m>=1`. It uses the actual constructed Piece. Combining it with `exists_pieces` removes that intermediate input. The constant is literally `densityConstant` with original physical `B`; no width realization factor enters. Its `A^(-1/2)` dependence remains intact. There is no bounded tube-position hypothesis.

The fixed-depth statement is now a theorem about arbitrary measurable shadings. Root-owned logarithmic algebra and the final composition supply constants independent of actual depth/scale/density/cap. Fixed or logarithmic density-ratio normalization is separate subsequent work, as are generic fixed separation/width/length geometry adapters; this report does not claim those are already part of the comparable-input statement.
