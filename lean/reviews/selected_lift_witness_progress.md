# Selected centered-lift witnesses and exact grouped energy

`SelectedLiftWitness.lean` closes the concrete witness/energy-position adapter identified in the earlier pivot interface review. It contains 16 proved theorems, seven definitions and one type abbreviation; it imports the frozen `SlabNormalization` module and leaves all shared files unchanged.

## Actual centered-grid witnesses

`splitCell` represents a full `(k+1)`-dimensional cell label in the energy convention `(horizontal k-cell, vertical integer)`. Its injectivity is proved. It does not round the point again and does not replace the original centered `GridCells.label` by a lower-corner label.

`split_lift_rounding` derives both horizontal and vertical errors of an actual `SelectedFiberLift.liftedCell` from Euclidean grid rounding and the true coordinate projections. `attach` then constructs `PivotWitnesses.AttachedSample` from an actual reference `LabeledPair`, one original sample `LabeledPair` in its common-pivot fiber, and the original intermediate label with its actual projection-closeness proof. The common error constant is

`C0 = pairWidth + (k+1)/2`.

The definition derives reference-pivot, sample-pivot, endpoint, intermediate and lifted-cell closeness. The only supplied fiber condition is equality of their actual rounded pivot labels. `attach_label` proves that the witness has exactly the original endpoint/pivot triple and the split actual lifted-cell label. No endpoint label is identified with its projection, no different angle is attached, and no geometric counting conclusion is assumed.

`retained_cell_sample` proves that a cell retained inside the common shifted selected shading has a representative sample in the same original finite raw fiber, whose literal original lifted label is recovered by undoing that shift.

## Common shifts and original energy positions

`unshiftCell delta j` is the exact inverse of the common integral vertical label shift from `SlabNormalization`. Both inverse identities hold without a reciprocal-integer mesh assumption.

For a grouped position `((pivotCell,j), shiftedCell)`, `originalPosition` is

`(pivotCell, splitCell(unshiftCell delta j shiftedCell))`.

`LegalPosition` records the actual original center-height condition `j <= delta z_0 < j+1`. This follows immediately from the selected cell's original slab membership. `originalPosition_injective` proves injectivity on these legal positions. In particular, equal original lifted cells force equal original slab indices by their actual half-open center intervals; after that, the common shift is invertible. The proof does not assume that the slab label is determined by the cell and does not charge an extra slab-count factor.

`grouped_energy_equals_original` proves equality of the sums of **actual squared incidence degrees** between original pivot/lifted-cell positions and original-group/translated-cell positions. It permits arbitrary finite incidence index types and only requires legality on the actual retained set.

## Precise closing-energy theorem

`fiber_weight_sum` proves that summing actual triple/lift support-label multiplicities over one energy position is exactly that position's degree in the original incidence set. `attached_sample_degree_energy` rewrites the existing geometric `finite_sample_energy` theorem into actual degree energy.

The final theorem `grouped_attached_sample_energy` takes:

- the actual finite retained incidence set `S`;
- its actual attached original samples;
- its original-group/translated-cell position map;
- original endpoint occupancy;
- actual legal position intervals and actual position correspondence;
- `0<delta<=1`, `C>=0`, `0<kappa<=1`, and `2 C delta <= kappa^5/4`.

It proves

`#S^2 <= #occupied^2 * pivotCount * liftCount * sum_position degree(S,position)^2`,

with the explicit geometric factors

`pivotCount k delta (4 C) (2+2 C)` and

`liftCount k delta (2 C delta) (4(2 C delta)/kappa^2) (kappa^3) (2/kappa)`.

The energy on the right is exactly the quantity controlled by grouped high-cell pruning. No generic energy upper/lower comparison, support count, pivot-segment premise, or rounded-triple residual bound is assumed. Those geometric facts come from the actual attached-sample theorem, and all finite energy equalities are proved here.

For witnesses from `attach`, use `C=C0` above and the corresponding explicit strengthened small-scale condition `2 C0 delta <= kappa^5/4`. The existing `PivotSupport.pivotCount_scale_bound` and `normalized_liftCount_bound`, with the latter applied at `2 C0`, expose the inverse-scale and inverse-fifth-power factors; their scalar substitution is left to the final pivot assembly.

## Remaining interface

The global selected-output/group/color reindexing is separate work. It must supply the actual retained incidence index, its endpoint sample and original grouped normalized-cell position. This module supplies the local pullback and witness construction and proves the precise equality needed to connect its grouped pruning energy with the geometric lower energy. It does not assert that the final global pivot theorem is already assembled.

## Verification

Compilation and `.olean` generation are clean, with no warnings. Seven main axiom reports contain only `propext`, `Classical.choice`, and `Quot.sound`. No `sorry`, `admit`, or custom axiom appears. Compiler and axiom log: `audit_work/selected_lift_witness_compile.log`.
