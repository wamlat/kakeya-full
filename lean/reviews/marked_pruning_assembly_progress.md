# Original marked input through actual spatial pruning and recovery

`MarkedPruningAssembly.lean` contains the input-facing `RecoveredInput` record and four proved theorems. It composes the actual base-estimate spatial pruning with the complete marked recovery. No frozen/shared files were edited.

## Uniform analytic constant and literal pruning data

`construct` starts from `DiscreteEstimate (k+1) m d p`, with `m,d >= 0`, `p >= 1`, fixed width/radius and positive error. It chooses the positive constant `K` before the original family, its tube count, the occupied comparison set, scale, cap coefficient, density, marked fraction, full two-ends parameters and marked angular radius.

For the original marked fraction `xi>0`, it applies `MarkedSpatialPruning.discrete_spatial_pruning_budget` with the actual loss budget `loss=xi/100`. It returns the original dyadic depth `J` and exactly

`eta = (xi/100)/(J+1)`

`L = max 1 (K #E A delta^(d-m-eps) eta^(-(p+1)) lambda^(-p)/M)`.

The pruned family is literally `O = PrunedIncidence.family F E delta L d J`. The output preserves its unchanged original tubes, actual shading subsets, original occupied comparison set, actual full deletion budget

`delta sum_i #(F.shade_i \ O.shade_i) <= (xi/100) lambda M`,

and the original small-radius ball estimate on `O.unionCells` for every `delta <= r <= 1`, with coefficient `coverConstant(k+1,1) 2^d L`. No original `M`, `E`, `J`, cutoff or spatial-bound parameter is replaced by a recovered comparison value.

## Actual recovered input record

The theorem constructs `RecoveredInput F O originalMarks E ...`. Its data and proved fields include:

- an actual positive selected tube count `N <= M`;
- an injective map `Fin N -> Fin M` into the original tube indices;
- a positive density `lambda'` equal to `lambda/2` or `lambda`;
- an actual family `G` whose tube is exactly `F.tube(index i)` and whose full shading is exactly `O.shade(index i)`;
- actual retained marks, subsets both of those full shadings and of the corresponding original marked shadings;
- `Comparable delta lambda'`, original width admissibility, delta separation, bounded bases and the original absolute cap bound;
- full-shading two ends with constant `2 B`;
- same-radius marked half-broadness at every cell;
- actual union inclusions `G.unionCells subset O.unionCells subset E`, a nonempty recovered union, and a positive original comparison cardinality `#E`.

In particular, the record's `full_eq` field states literal equality with the original spatial-pruning output shading. Neither the density-bin choice nor the marked-cell filter makes any further full-cell deletion on a retained tube.

## Derived marked population on the exact chosen H

The original marked hypothesis is only

`xi lambda M/delta <= sum_i #originalMarks_i`.

Together with the constructed deletion budget and the proved recovery bound `W/4-2R`, `marked_budget` derives

`xi lambda M/(8 delta) <= sum_i #retainedMarks_i`.

`marked_union_mass` proves exact incidence double counting over `H=G.unionCells`. Hence the record returns the bound directly in the downstream form

`xi lambda M/(8 delta) <= sum_{z in G.unionCells} #incident(markedFamily G marks,z)`.

The original `M` and original `lambda` remain in this lower bound. The positive selected count and positive occupied comparison cardinality are derived; they are not assumed as recovered-family input premises.

## Scope and downstream use

The input full family must be actually comparable, admissible, separated, bounded and cap controlled. Original marks are actual subsets of the original full shadings, with the original one-tenth cap bound at the fixed radius `theta`. The full two-ends tests are required on the original family. All pruning, recovery, new geometry, marked half-broadness and retained population conclusions are derived.

For `MarkedPivotSelection.construct`, take the recovered record's `family`, `marks`, `H=family.unionCells`, density `record.density`, `B'=2B`, original comparison `E=#E`, and `I=xi lambda M/(8 delta)`. Its geometry, density, marked incidence, cap-half and two-ends hypotheses are the record fields. The cardinality comparison for H follows from `union_subset_E`. The fixed width, positive alpha/theta and kappa small-scale tests remain the separate uniform choices handled by the surrounding pivot argument.

This module does not assume an output count, legal sample system, collision bound or final pivot estimate. It closes the original marked input to actual recovered input assembly and retains the spatial data needed by the later graph-cap argument.

## Verification

The file compiles without warnings, and its `.olean` is built. All four principal theorem axiom reports use only `propext`, `Classical.choice`, and `Quot.sound`; there are no `sorry`, `admit`, or custom axioms. Log: `audit_work/marked_pruning_assembly_compile.log`.
