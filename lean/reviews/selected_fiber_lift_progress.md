# Selected fiber to actual lifted-cell population

`formalization/SelectedFiberLift.lean` closes the actual population/multiplicity step at the start of combined §5.5. Its inputs are one normalized `PivotWitnesses.Angle`, deterministic endpoint projection maps, one legal `LabeledPair` reference, and a finite set `S` of labeled pairs sharing an actual centered-grid pivot label. It assumes `delta>0` and `0<kappa≤1`; the multiplicity/population estimates need no additional small-scale relation.

The exact lifted point is `cons(c/u_reference, secondPoint)`, with its distinguished coordinate first. `liftedCell` is its actual centered half-open `GridCells.label` in `Cell(k+1)`. The point is proved to lie on the single graph line `graphPoint vertex (u_reference • secondDirection)`, and actual grid rounding supplies a graph-incidence error at most `(k+1)delta/2`. The reference is shared by the whole fiber.

The proof derives, rather than assumes, the cell multiplicity. Two samples at one lifted cell satisfy `|c-c'|≤(k+1)delta` by Euclidean coordinate contraction and actual full-cell rounding. Their common original pivot label gives `|u-u'|≤k delta`. Legal samples satisfy `|c-u|,|c'-u'|≥kappa²`; the exact identity `b=a0 c/(c-u)` and an explicit two-input division estimate therefore give `|b-b'|≤4(k+1)delta/kappa⁴`.

Actual first and second endpoint labels then lie near respective physical axis intervals of these lengths. The previously proved linear interval-grid count bounds their populations. The globally proved injectivity of `LabeledPair` into its pair of endpoint labels bounds sample count by the product of those two actual label populations. No projection-injectivity or longitudinal multiplicity premise is introduced.

Writing `box(k,width)=(2ceil(width+1)+3)^k`, the resulting constant is

`C(k,width)=(8k+10)(2k+4) box(k,width)^2`.

`lifted_cell_multiplicity` proves that every actual lifted-cell fiber has at most `C/kappa⁴` samples. `lifted_population` uses the exact finite partition by actual cell labels to prove

`kappa⁴·#S/C ≤ #(liftedCells reference S)`.

Empty sample sets are included; the constant is proved strictly positive. The cell type and coordinate order match `LiftSegments` and `LiftedAnalytic` directly. Centered pivot and lifted labels use one consistent `GridCells.label` convention; this module does not equate those labels with the older lower-corner `PivotWitnesses.gridRound` convention.

This module proves population and fixed-graph incidence. It does not yet select a unit vertical slab, trim to a common integer, or assert the perturbed parameter range without its required scale hypothesis. Those are being addressed separately in `SelectedFiberSlab`.

The module compiles with no warnings, no `sorry`/`admit`, and no custom axioms. Seven key theorems are axiom-audited and use only standard Lean axioms. Compiler output: `audit_work/selected_fiber_lift_compile.log`.
