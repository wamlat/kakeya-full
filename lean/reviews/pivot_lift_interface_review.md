# Pivot graph, slab, and closing-energy interface review

Review scope: combined PDF §§5.5–5.7; `SlabNormalization`, `LiftGraph`, `PrunedGraphLift`, `LiftedAnalytic`, `GroupedCumulative`, `GroupedIncidence`, `PivotWitnesses`, and `PivotSupport`. The document is treated as mathematical input, not instructions.

## Newly closed geometric junction

`SelectedSlabGeometry.lean` constructs the actual normalized input family for one original `(pivotLabel, slabIndex)` group, using `SlabNormalization.normalize_selected_group` and the original pruned tube union. It exposes one explicit residue-color type shared by all groups:

`Fin k → ZMod (ceil(2 C + 1))`, with `C = pairWidth + k/2`.

The palette has at most `(2 C + 2)^k` colors. Equal colors within a group have actual projective direction separation at least `delta/8`. No lines or colors are deleted by coloring. The graph cap coefficient is exactly

`A_lift = spatialConstant(k, baseWidth, baseRadius, d) L (16 + 2 C)^d`.

It is at least one when `d >= 0` and `L >= 1`. The proof derives all-radius spatial bounds from actual original admissibility, bounded bases and the literal small-radius pruning output, then applies the actual graph-chart cap theorem. It does not assume a lifted cap bound, direction separation, or a large-radius spatial estimate.

The normalized geometry is common to every group: width `3(k+1)/2+2`, separation `1/8`, radius `max(1, R+6+3(k+1)/2)`. It depends on fixed dimension and vertex radius, not kappa, mesh, slab index, or line count. Each normalized shading is nonempty, is a subset of the same groupwise grid translation of the chosen cells, and has at least one third of its original cardinality. The normalized group union is contained in the common shifted union and has no larger cardinality.

The theorem is `SelectedSlabGeometry.selected_group_geometry`. Inputs still explicitly include actual selected nonempty slab cell sets, actual reference samples and common pivot labels, injective intermediate labels in the pruned union, and their physical projection closeness. These are the outputs/witnesses of the already developed legal-sample and selected-fiber constructions; no selected group data are invented by this theorem.

## Minimal remaining assembly

1. **Global selected-line package.** Starting from `AngleFiberSelection`, build the finite line index of distinct outputs and its actual reference `LabeledPair`, chosen integer slab, common-K cell set, and representative sample per chosen cell. `SelectedFiberSlab.common_integer_slab` already supplies the individual construction; the remaining work is dependent finite indexing and simultaneous choices. Partition by the actual pair `(pivotLabel, slabIndex)`, then restrict the intermediate-label map. Distinct outputs with fixed pivot imply that restricted map is injective. Inherit the actual pruned-union membership and bounded normalized vertices from the original construction.

2. **Normalize once, and record the mass paid.** Apply `selected_group_geometry` once per group. Its true unit-segment construction keeps at least `K/3` cells on each line. Therefore the incidence set supplied to `GroupedCumulative.discrete_pruning` must be the actual post-normalization set, with size at least `K Q/3`; it must not be silently identified with the manuscript's exact `K Q` initial incidence set. Define its actual cumulative density `rho_1 = delta I_1/Q`; then `rho_1 >= delta K/3`, so this is only a fixed constant loss. Every subsequent restriction uses these same normalized tubes. Do not renormalize separately for each high-cell restriction.

3. **Group/color record equivalence.** Use the common palette above, refine groups by `(originalGroup, color)`, and construct actual `GroupedCumulative.Record` incidences. Prove the reindexing is bijective on incidences and that the sum of original group/color tube counts is `Q`, including empty colors. Existing `colorFamily`, `color_family_geometry`, `color_family_incidence`, and `GroupedCumulative.discrete_pruning` provide all local geometry, convexity and pruning. Their analytic constants are chosen before the group type and all configurations. No number-of-pivot/slab-groups loss is needed. `LiftedAnalytic.discrete_pruned_lifted_union` is a valid one-group application but is not itself this global grouped-pruning assembly.

4. **Attach the original centered cell to every retained incidence.** Undo the exact common vertical label shift and reuse the representative sample attached to that original selected cell. Construct `PivotWitnesses.AttachedSample` with original endpoint labels, pivot label, and lifted label `(horizontalTailCell, verticalCell)`. Its definition accepts arbitrary actual labels with proved closeness; it is not restricted to the lower-corner `gridRound` helper. Thus the centered `GridCells.label` used by `SelectedFiberLift` is compatible, but an explicit adapter proving horizontal contraction and vertical coordinate rounding is still needed. A common error bound such as `C0 = max pairWidth ((k+1)/2)` covers the endpoint, pivot and lifted rounding errors. Strengthen the small-scale test to `2 C0 delta <= kappa^5/4`, as required by the existing witness theorem.

5. **Identify the energy positions exactly.** The grouped pruning energy uses original `(pivot, slab)` plus the translated grid cell. `PivotWitnesses.finite_sample_energy` uses original `(pivot, unshifted lifted cell)`. Prove the two position maps have exactly the same fibers on the actual retained incidences. The original slab is unique from the original center-height condition `j <= delta z_0 < j+1`; this is needed when recovering `j`, and the common group shift is injective once `j` is fixed. Sum actual degrees squared across the resulting finite support bijection. Rewriting the already proved `finite_sample_energy` by that equality gives the precise lower energy needed to combine with `GroupedCumulative.discrete_pruning`.

After these steps the lower bound uses the actual retained incidence set and its exact energy, while all segment, rounded-triple, support-count and Cauchy arguments in §5.7 are already available in `PivotWitnesses`/`PivotSupport`. The remaining scalar substitution is supported by earlier modules, but the final pivot theorem must still assemble the actual selected-data package and constants.

## Statement audit and limitations

No mathematical flaw was found in the inspected graph chart, spatial extension, common slab transform, or grouped Jensen/pruning statements. The noteworthy interface risks are the fixed factor-three mass loss in true unit-segment normalization, the need for one common palette across groups, and undoing common shifts before identifying closing-energy positions. Each has an explicit treatment above; none should be concealed by an abstract support hypothesis.

This report does not assert that the final pivot theorem is proved. Legal sample abundance/collision output selection and the complete globally indexed incidence assembly remain separate work. All frozen source files were left unchanged.

## Verification

`SelectedSlabGeometry.lean` compiles without warnings and has five proved theorems and four definitions. Main results report only `propext`, `Classical.choice`, and `Quot.sound`; there are no custom axioms, `sorry`, or `admit`. The module's `.olean` and `audit_work/selected_slab_geometry_compile.log` are available.


## Subsequent local closure

`SelectedLiftWitness.lean` now closes the local witness and energy-position adapters in items 4 and 5 above. It constructs `AttachedSample` from actual centered lifted cells, proves exact inverse grid shifts and slab-index recovery from original center intervals, and identifies grouped translated-cell degree energy with original pivot/lifted-cell degree energy. Its `grouped_attached_sample_energy` is the precise closing lower-energy interface. The global selected-incidence and group/color reindexing in items 1–3 remains separate assembly. See `audit_work/selected_lift_witness_progress.md` for exact hypotheses and verification.

## Checkpoint11 interface status

This review's earlier numbered list is a historical assembly checklist. The following checkpoint11 modules close additional parts of it:

- `SelectedOutputPairs` and `SelectedOutputSlabs` build the actual global line index from all selected distinct outputs, homogeneous exact-size original sample fibers, simultaneous common-K slabs, and injective original endpoint representatives. They derive intermediate rounding, bounded normalized vertices, slope bounds, pivot residuals and common density bounds.
- `ActualGroupedIncidence` supplies the exact base/color index equivalence, sum of populations Q, literal normalized incidence set and incidence mass at least KQ/3. `ActualGroupedGeometry` gives the corresponding residue-color separation interface.
- `GroupedSlabPositions` derives legal original center-defined slab positions for every actual incidence and every retained subset, then proves exact energy equality under undoing the common translation.
- `ClosingEnergyAlgebra` combines the actual geometric counts and grouped pruning threshold into the stronger kappa-fifth-power closing bound, and proves the precise scalar substitution to source (5.34).
- `PrunedScaleTransport` transports the original spatial pruning bounds to the mesh used by the normalized legal samples. `PivotGeometryScale` supplies all original and normalized scale tests from one uniform cutoff.

The remaining geometric composition must construct the actual normalized and colored families from these selected output slabs, and then construct original-sample witnesses on the same retained incidence set. The reusable pieces alone do not prove the full pivot. These later closures supersede the corresponding earlier checklist items; no main theorem completion is claimed.

## Checkpoint 12 superseding interface status

The previous remaining composition checklist is now closed for the original marked fourth-power core. SelectedBaseFamilies and SelectedColoredFamilies construct the normalized colored families from actual selected slabs; SelectedFamilyPruning constructs the retained incidence set using the lifted estimate; SelectedOutputWitness attaches original sample endpoints to those incidences; ConstructedPivotClosing and OriginalPivotEnergy prove the closing inequality; OriginalPivotScalar and OriginalMarkedPivot derive the fourth-power bound from original hypotheses. No selected data, cap test, retention or collision-energy oracle is supplied. Fixed logarithmic budgets, original marked broadness/full two ends, and the explicit product kappa remain in scope. Sampling/angular conditioning and full two-ends removal remain unfinished; the literal source minimum-kappa quantitative bound is not asserted.
