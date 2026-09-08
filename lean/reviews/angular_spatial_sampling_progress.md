# Actual angular refinement to every spatial sampling input

`formalization/AngularSpatialSampling.lean` is complete, clean-built, and frozen. Only this new module and its own audit/report files were written. Imports are `SpatialGridPopulation`, `AnisotropicSamplingRetention`, `MeasurableToDiscrete`, and `TransformedGridSupport`; no registry or shared source was edited.

The input is an actual `AngularRestrictedRefinement.Refinement V` of an existing group `g ∈ P.groups`. `construct` also takes original admissibility, separation, bounded bases and real-cap bound, positive mesh, original density at most one, `B ≥ 1`, nonnegative two-ends exponent, positive broadness exponent, nonnegative cap exponent/coefficient, and the explicit fixed test `2 ≤ widthFactor(k+1,width)^(k+1)`. It does not take a box, population, broadness, selected family, or sampling-input oracle.

For W=widthFactor(k+1,width), it uses exactly:

- physical density `physicalDensity = V.density/W^(k+1)`;
- spatial marked ratio `a = 1/[4(V.depth+1)]`;
- spatial overlap `Csp = ActualSpatialMarked.overlapConstant k 1 3`;
- literal good boxes `SpatialMarkedGroups.good` at full mass `physicalDensity*delta^k` and marked ratio `a`;
- per-good-box marked ratio `a/4`;
- effective anisotropic retention `e = AnisotropicSamplingInput.retention k 3 (a/4)`;
- full two-ends coefficient `((B*(4/P.eta))*(1+(k+1)/2)^alpha)*W^alpha`;
- marked broadness coefficient `((broadCoefficient k beta*(8/P.eta))*(2(V.depth+1)))*(4*Csp)`.

The common spatial box dimensions are exactly `(R+2,k+4)` with angular width three and physical tube width one. Original-index composition is injective. `refined_geometry` derives separation/cap/location from the original family; `spatial_data` constructs common boxes from the literal actual base labels. Full sets remain the unchanged refined Ref sets on their spatial indices. Marks are the previously proved proportional filter of the actual original refined marks, so broadness is transferred by a theorem, not presumed to survive thinning.

`Package.spatial` retains ALL good boxes and proves their summed tube population is at least `a*V.N/4`, and their summed marked mass is at least `a*physicalDensity*delta^k*V.N/2`. Every good box has a positive population and marked mass at least `(a/4)*physicalDensity*delta^k*Mq`.

`Package.output` simultaneously constructs an actual `AnisotropicSamplingRetention.Output` for every such box. Its final full and marked measurable shadings, injective index, exact two-to-four physical mass normalization, density bounds, full two ends, marked broadness, rescaled separation/cap, effective retention, and population retention are those of the existing constructive theorem, on the same full/marked data. Its base bound is `baseBound 3 (R+2) (k+4)`, and cap coefficient is `capFactor k 3 m*A`.

`box_full_support` proves the exact old-support premise needed by `AnisotropicHighDensity`: each pre-output box Full set lies in `normalizedSet W (cellUnion delta (refinedCells V width q))`. `old_cell_support` and `Package.old_support` prove each actual output Full set lies in the SAME common `pieceMap u tau W q` image of these old cells. There is no separate map per output tube. `box_comparable` keeps the finite old shadings comparable at V.density, and `box_cells_eq` identifies their finite union literally with `refinedCells`; these are available for the coarse angular case.

`Package.old_count` gives the summed original-grid count over every good box at most `Csp*card((P.family g).unionCells)`. `total_old_count` gives the full angular/spatial sum at most `Csp*2*tau^(-beta)*card(F.unionCells)`. No overlap premise on sampled cubes or their pullbacks appears.

The physical density bound is explicitly proved from `V.density ≤ 2*originalLambda ≤ 2 ≤ W^(k+1)`. It is not silently clamped. Remaining scope: the theorem starts with actual V, rather than constructing the initial angular decomposition/refinement; it does not derive the scale-only budgets for its displayed conditioning constants, decide coarse/low/high-density angular cases, apply or sum their analytic bounds, or remove two ends. Those are separate downstream tasks. No unpublished analytic result is used as an assumption.

Verification: clean `.olean` compilation under Lean 4.33.1, no warnings. Fresh complete-source audit checks all 34 explicit declarations (20 theorems, 11 definitions, one abbreviation, two structures), exact source-prefix identity, and standard axioms only (`propext`, `Classical.choice`, `Quot.sound`). Files: `angular_spatial_sampling_full_source_audit.lean`, `.log`, and `angular_spatial_sampling_audit_manifest.json`. Source SHA-256: `4303c9795e206b5b215f8e2b89b3ec6a0728ec032b91f36797d2e7549bbaad3c`.
