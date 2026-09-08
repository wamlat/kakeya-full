# Independent review: completed-measure representatives and spatial decomposition

Read-only review of final development sources:

| Source | SHA-256 |
|---|---|
| `LebesgueRepresentatives.lean` | `0384ebb173ae149fe7fc253d2b4b9fda0fd10797505c66ae5ec5865933250523` |
| `LebesgueAngularSpatial.lean` | `d1dad9395442f6a89a1338bc4c4f8acd09a219315fb17299d9b463cac45a98d7` |

No mathematical or statement defect found. This is an independent source review, not a duplicate of the owning agent's compiler/axiom audit. These sources are outside the original 406-source freeze.

`LebesgueRepresentatives.construct` begins with `NullMeasurableSet` for each original full and marked set. It chooses genuine measurable subsets, not arbitrary a.e.-equivalent sets that could leave the original carrier. Intersecting the chosen marked subset with the chosen full subset enforces actual nesting and changes no marked measure because the original marks are contained in the original full shading. Every subsequent measure and intersection identity follows from this exact a.e. equality. No completeness, finite total measure, or finite individual measure is needed for these equalities.

The finite family yields one common a.e. membership event for every original index, and hence identical full/marked finite incidence rows. `transfer_ae` can therefore move a statement quantifying over all angular centers/radii at once; it does not incorrectly take an uncountable union of null exceptional sets. Actual subset containment remains pointwise. The union and intersection identities also remain valid for nonmeasurable test sets, since their proof uses the common a.e. membership identity. The real-valued measure equalities do not claim finiteness; consumers obtain finiteness from their actual bounded carriers.

`LebesgueAngularSpatial.restoreInput` changes only the input reference in the existing `Pieces` record. Selected sets, groups, scale, assignment, depth, broadness and overlap are unchanged. The old-input containment follows by transitivity through the actual Borel subset, and total mass is replaced by an equality. The public `construct` creates the existing variable-length decomposition on these representatives and returns a decomposition indexed by the original input, with the same actual pieces. Retention, entire-carrier spatial containment, pointwise broadness and overlap are inherited rather than assumed. Empty families and zero-measure incidences are allowed. The fixed upper-length, width, scale and beta ranges agree with the existing Borel constructor.

This closes the completed-Lebesgue scope of the actual angular/spatial construction. It does not alone change other public predicates requiring `MeasurableSet`; those need their separate consumer wrappers.
