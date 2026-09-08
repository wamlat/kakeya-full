# Actual Gaussian collision graph selection

Source: combined PDF §2.1, the independent-set extraction after the expected collision bound. Frozen module `GaussianCollisionSelection.lean`, SHA-256 `23a7af20dd78d04e7c4d0c98f89a49ebcca9d1d4f637316d6f3e59132d556952`.

## Exact construction and theorem

`good F omega` is exactly `GaussianGoodDirections.goodIndices` on the original indexed directions, with image-norm cutoff1/4. `graph F delta omega` is a literal SimpleGraph on the subtype of these actual original indices. Its adjacency means distinct vertices and actual projected unoriented angle<=delta. Symmetry is proved from the real inner product; loops are excluded by the original distinctness test.

Under the sole sample condition `||GaussianLinearOperator.operator omega|| <= 20`, `orderedCount_le` maps each actual graph ordered edge to its original ordered pair `(i.val,j.val)`. This map is injective. Both nonzero-output tests in the original collision event follow from actual good membership and the positive cutoff1/4. Thus the graph count is bounded by the **actual** `GaussianCollisionExpectation.orderedCollisions F 20 delta omega` cardinality, without a supplied edge-count comparison.

`select` invokes the proved finite graph independent-set theorem, then takes the injective image of that actual independent Finset under the original-index map. It returns one original-index Finset S with:

- S contained in the literal good index set;
- every distinct pair of selected projected directions has actual angle strictly greater than delta;
- consequently their projective chord distance is at least `(2/pi)*delta`;
- the exact cardinality lower bound

`|good|^2 / (|good| + |original orderedCollisions|) <= |S|`.

The denominator contains the ordered count once. The graph theorem already proved ordered count=twice unordered edges, so there is no extra factor2. The good-empty case is explicit: numerator0 makes the stated lower bound0, including the zero-denominator case. In the nonempty branch, the denominator is proved positive before monotonic division is used.

No original cap, separation, density, probability, positive population, or expected-count hypothesis is used by this deterministic extraction. Those enter the separate Gaussian-realization and population-algebra assembly. The source does not construct projected shadings or assert their geometry here; scalar's separately reviewed ProjectedGridFamily supplies those actual image sets.

## Verification

The module compiles to .olean with zero diagnostics. The requested **production all-local exact-source audit** was run using `audit_operator_subset.py`, including generated local declarations: PASS, 7 theorem entries and 9 total local declarations. All dependencies use only `propext`, `Classical.choice`, and `Quot.sound`.

Evidence: `GaussianCollisionSelection_operator_audit.json`, `GaussianCollisionSelection_operator_audit.log`, and the generated exact-source `formalization/GaussianCollisionSelection_OperatorAudit.lean`. The frozen source hash was checked after audit completion. No frozen/shared proof source or registry was edited.

Scalar independently read the same final bytes with no defect; its unique report is `gaussian_collision_selection_scalar_review.md`. I also checked the matching population coefficient calculation independently in `gaussian_selection_algebra_finite_review.md`.
