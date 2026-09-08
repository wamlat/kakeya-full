# Completed-measurability representatives and spatial decomposition

These two new modules close the finite nested representative construction and literal measurable angular/spatial output identified as narrower in frozen checkpoint 22. They are outside the frozen 406-module snapshot and do not change its source or verification record.

`LebesgueRepresentatives.construct` works for any measure space and finite original families Full/G with `NullMeasurableSet` and G_i subset Full_i. It chooses measurable subsets using Mathlib's existing `NullMeasurableSet.exists_measurable_subset_ae_eq`, then intersects each selected marked representative with the same selected full representative. Its `Output` has actual subset/nesting fields and individual a.e. identities, with no finite-measure, completeness, or SFinite hypothesis.

The derived methods preserve full/marked individual measures, arbitrary set-intersection measures, union measures, their real-valued versions, and summed real masses exactly. A single a.e. event identifies all original full and marked membership predicates simultaneously. `rows_ae` identifies both actual finite incidence rows; `transfer_ae` transfers any predicate of those rows, allowing all angular centers and radii to be quantified inside one event. No pointwise equality on an exceptional null set is asserted.

`LebesgueAngularSpatial.construct` is the actual consumer. It takes completed-Lebesgue-measurable Y_i on original variable-length carriers and returns precisely `MeasurableAngularSpatialLengths.Decomposition F Y lengths delta beta width upperLength`, with the original Y in the result type. It constructs the Borel subset representative, invokes the proved angular/spatial construction, and changes only its input reference using exact total mass equality and actual subset containment. All selected shadings, groups, assignments and scales remain unchanged. The final shadings are actual Borel subsets of original Y, with pointwise broadness, pointwise overlap, exact original logarithmic mass retention, disjoint original indices, and entire-original-carrier containment. Empty finite families and zero mass are inherited from the original constructor. Only a fixed length upper bound is required; no positive lower length or global bounded-position premise is added.

Both production files compiled cleanly with no diagnostics. The unchanged-source environment auditor then reported only `Classical.choice`, `Quot.sound`, and `propext`, with no custom axiom, sorry, native decision or missing named declaration. It audited 35 theorem/49 all-local declarations for LebesgueRepresentatives, and 5 theorem/6 all-local declarations for LebesgueAngularSpatial. Exact logs and dependency inventories are in `LebesgueRepresentatives_operator_audit.{json,log}` and `LebesgueAngularSpatial_operator_audit.{json,log}`.

Final SHA-256:

- LebesgueRepresentatives.lean: `0384ebb173ae149fe7fc253d2b4b9fda0fd10797505c66ae5ec5865933250523`
- LebesgueAngularSpatial.lean: `d1dad9395442f6a89a1338bc4c4f8acd09a219315fb17299d9b463cac45a98d7`

The source-to-completed-measure interfaces for final maximal and real-cap estimates are owned by root; the literal original raw sampling support/law transfer is owned by the finite agent. These two files do not assert those separate consumer theorems. In particular, the exact raw cell-weight identity follows from the intersection equality here, but the complete original-input sampling record still must be transported in its own adapter.
