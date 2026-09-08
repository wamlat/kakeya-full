# Actual marked recovery after spatial pruning

`MarkedPruningRecovery.lean` contains 15 proved theorems and nine definitions. It closes the bounded recovery step after arbitrary full-shading deletion while keeping full shadings and marked incidences distinct. All frozen/shared files are unchanged.

## Actual finite construction

Inputs are an original actual `TubeFamily F`, its full finite shadings `Y_i=F.shade_i`, arbitrary surviving full shadings `O_i subset Y_i`, and original marks `Z_i subset Y_i`. The original full family is comparable at `(delta,lambda)`.

Define the actual deleted full incidence mass

`R = sum_i #(Y_i \ O_i)`

and original marked mass `W = sum_i #Z_i`. No retained-mass conclusion or abstract deletion count is assumed.

1. Keep exactly those original tube indices satisfying `#Y_i <= 2 #O_i`. A pointwise counting argument proves that deleting full cells and then discarding the other tubes removes at most `2 R` original marks in total. It does not count already deleted full cells twice.
2. Partition these good tubes by `#O_i <= lambda/delta` versus `#O_i > lambda/delta`. Choose the bin carrying at least half the surviving marked mass. Every full shading in the first bin is comparable at density `lambda/2`; every full shading in the second is comparable at density `lambda`. No further full-shading cells are deleted or trimmed.
3. At a cell, compare the original marked row `m0` with the current marked row `mT` on the chosen bin. Keep marks exactly where `m0 <= 4 mT`. The cells failing this test carry at most `W/4` current marks. The retained marks on tube `i` are literally `(Z_i intersect O_i) intersect keptCells`.

The stronger internal result is retained marked mass at least `W/4-R`. The final `recover` theorem returns the requested coarser lower bound `W/4-2R`. This allows direct substitution of the actual deletion budget supplied by `MarkedSpatialPruning`.

## Actual output family and geometry

`recover` constructs a density `lambda'` equal to `lambda/2` or `lambda`, and an actual finite selected index set `T` with `#T <= M`. `selectedIndex T : Fin #T -> Fin M` is proved injective. The resulting `selectedFamily F O T` uses the original tubes and exactly their full surviving shadings `O_i`.

The theorem proves:

- positive `lambda'` and actual `Comparable delta lambda'`;
- the retained marked mass bound after exact reindexing;
- each retained marked shading is a subset of its selected full shading and of its original marked shading;
- same-radius marked cap fraction at most `2/5` on every cell;
- inherited full-shading two ends with constant `2 B` at every original test ball.

`selected_geometry` proves original admissibility, separation, bounded bases, cap bounds and occupied-union inclusion for this same constructed family by an actual injective tube restriction. It does not assume inherited geometry.

## Broadness remains a marked statement

The broadness input is the actual original marked row: every unit-centered projective cap of the fixed radius `theta` contains at most one tenth of its marks. The retained row is a subset of the original marked row, and the kept-cell test gives `m0 <= 4 mT`, so the new fraction is at most `4/10 = 2/5`.

The proof is about the actual **marked** reindexed family. It does not assert broadness of all full-shading incidences. Outside the kept marked-cell set, the new marked row is empty, so the all-cell statement holds there as well. The strict cap condition is `projectiveDistance < theta`, matching the downstream `MarkedSubsetSamples` interface; `2/5 <= 1/2` gives its required half-broadness test.

The full shadings retain original two ends because selected good tubes have `#Y_i <= 2 #O_i`; original physical-ball counts dominate those of `O_i`. The marked-cell filter is never applied to these full shadings.

## Precise remaining composition

Use `MarkedSpatialPruning.discrete_spatial_pruning_budget` to choose `O_i` and establish its actual deletion budget. Apply this module's `recover`, then `selected_geometry` for the inherited family geometry. The resulting actual marked half-broadness, marked mass, full comparable density and full two ends are the inputs for `MarkedSubsetSamples.construct`.

This module does not choose the upstream pruning loss or the downstream kappa. It proves the finite recovery uniformly for any actual deletion and the displayed original full/marked hypotheses. Thus smallness of the deletion relative to the original marked fraction remains an explicit scalar choice, rather than an assumed positive final marked mass.

## Verification

The module compiles and builds to `.olean` without warnings. Eight principal theorem axiom reports contain only `propext`, `Classical.choice`, and `Quot.sound`. There are no `sorry`, `admit`, or custom axioms. Compiler and axiom output: `audit_work/marked_pruning_recovery_compile.log`.
