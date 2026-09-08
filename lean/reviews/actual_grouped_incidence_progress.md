# Actual grouped incidence and slab-position bridge

All three modules are complete, clean-compiled, built, and frozen. They contain 29 theorems and 8 definitions. All 37 declarations passed fresh full-source axiom audits; each audit source was checked byte-for-byte against its current module prefix. No errors or warnings occurred, and the exact union of axioms is `propext`, `Classical.choice`, and `Quot.sound`.

The bounded bridge consists of `ActualGroupedIncidence.lean`, `ActualGroupedGeometry.lean`, and `GroupedSlabPositions.lean`. It formalizes the finite grouping, common color, exact incidence-count, and position bookkeeping in combined §5.6. It does not assert that the full endpoint argument has been assembled.

## Exact finite construction

For a finite type I of actual original output indices, a literal geometric base label `base : I → B` and one common color map `color : I → C`, the group type is the finite image of `(base i, color i)`. In the application, B is exactly `(pivot grid label, original unit slab index)`.

`indexEquiv` is an actual equivalence from the dependent sum of all groups' local Fin indices to I. Every original output occurs exactly once. No color is selected by a pigeonhole, no output is duplicated, and empty original families are handled. Consequently:

- the sum of group populations equals `Fintype.card I = Q`, both in natural and real arithmetic;
- `sum_original` preserves every additive weight, not just cardinality;
- an injective original `(pivot, intermediate)` output map gives injective intermediate labels within every pivot/slab/color group;
- actual reindexed tube and shading maps are literal pullbacks along this bijection.

`incidences` is the actual finite set of all pairs `(grouped original output index, normalized shaded cell)`. The proof establishes its membership characterization and exact identity `|S| = Σ_i |shade_i|`. Equal-cardinality trimmed slabs of size K and the already-proved unit-segment normalization retention `|shade_i| ≥ |trimmed_i|/3` give `|S| ≥ KQ/3`.

## Geometry and pruning

Admissibility, bounded tube bases, and cap bounds are inherited by injective reindexing. The cap input is an actual cap count over original indices sharing the same base label; it is not a support-cardinality or energy bound. The counted original indices and their directions are preserved literally.

`graph_family_separated` computes the common residue color from each actual original intermediate grid label. With the actual pivot residual at most Cδ, graph slopes of norm at most one, and injective original `(pivot, intermediate)` labels, every group is δ/8-separated. The same palette has at most `(2C+2)^k` colors in lifted ambient dimension k+1. The bound is independent of δ, κ, Q, and the number of pivot/slab groups.

`actual_discrete_pruning` invokes the proved `GroupedCumulative.discrete_pruning` on the constructed groups and literal S. It supplies a positive constant before all finite index types, counts, labels, colors, scales, cap coefficients, and actual tube/shading maps. It returns an actual subset T of S retaining more than half the incidence mass and the calibrated upper bound on the sum of squared multiplicities at `(base, normalized cell)`. The only analytic input is the stated `DiscreteEstimate`; no support or collision estimate is assumed.

## Exact original slab labels and energy

For each original index, `GroupedSlabPositions` assumes the actual output of slab/unit-segment normalization: its normalized shading is contained in the integral shift of its trimmed cells, and those trimmed cell centers lie in that original index's recorded unit slab. These facts derive `LegalPosition` at every constructed incidence and every retained subset T of S.

The existing independently proved injectivity of undoing the shift on legal positions then gives an exact equality between the grouped squared-multiplicity sum and the energy at `(original pivot label, original unshifted lifted-cell label)`. There is no additional slab multiplicity factor and no assumed energy comparison.

## Remaining application boundary

This is a fully proved finite/geometry adapter. It accepts actual normalized tube/shading maps, trimmed slabs, bounded graph slopes and their pivot residuals. The next application must choose and package those data for every output from `ActualLabelSelection.Selection`, `SelectedFiberSlab`, and the actual unit-segment geometry, then supply their already-proved properties. The original physical mesh δ and normalized legal-sample mesh δ/(1+2width) must remain distinct: use `PrunedScaleTransport` to transport the survivor-cell ball count, and do not reuse original tube admissibility at the changed mesh. Construction of all attached original endpoint samples for the retained incidences and the final scalar endpoint contradiction remain separate steps.
