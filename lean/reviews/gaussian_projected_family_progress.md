# Actual Gaussian-selected projected finite family

Frozen source `GaussianProjectedFamily.lean`, SHA-256 `ed86bcb0bd91f7a72cb18f60d38ec0a84ace44ff5728260eee7ba932fd98e900`. This composes the original Gaussian probability/graph selection with the independently proved common grid projection and same-tube fiber bounds.

## Public actual-input interface

`construct` takes only an original `F : TubeFamily 7 M`, 0<delta<=1, A>=1, original delta-separated directions, original cap-four bound with coefficient A, original admissibility at width*delta, and original bounded bases R. It returns `Nonempty (Output F delta A width R)`. There is no assumed projection, selected subset, retained population, projected carrier, fiber estimate or output cap/count premise.

The proof internally invokes `GaussianProjectedSelection.exists_projection`, takes its actual finite original-index subset S, and enumerates it by

`indexMap S i = (S.equivFin.symm i).val : Fin S.card -> Fin M`.

Injectivity and membership are proved. `restrictedFamily F S` has exactly the original same-index tubes and shadings, and its union is exactly `S.biUnion F.shade`, a subset of the original full union. The actual projected family is then obtained using ProjectedGridFamily at the same original mesh delta and one common `labelMap (operator omega) delta`.

## Output fields

- One actual Gaussian sample omega and finite original subset S; target `family : TubeFamily 5 S.card`.
- Actual matrix operator norm<=20.
- Projected bases exactly P(original bases), directions exactly P(original directions)/their norms.
- Every target row is exactly the common label-map image of its selected original row.
- Actual physical lengths exactly `||P(original direction)||`, lying in [1/4,20].
- Actual length-carrier incidence at width `(20*width+5/2)*delta`.
- Target projective-chord separation `(2/pi)*delta`, derived from the selected angular separation and the literal normalized output directions.
- Exact union identity `(S.biUnion F.shade).image(labelMap P delta)`, hence target union cardinality<=original F.unionCells cardinality.
- Each target row has cardinality at least original-row-cardinality divided by the proved positive constant `fiberConstant 7 5 (1/4) 20 width`, and at most its original row cardinality.
- Target bases bounded by20R.
- Actual population at least `GaussianProjectedSelection.retainedConstant*M/(A*log(2/delta))`.

The optional `density_bounds` theorem uses an original Comparable premise and returns the exact fixed interval `[lambda/(Cfiber*delta),2lambda/delta]`. It does not assert a strict factor-two output predicate or introduce extra shading cells. The later five-dimensional seed accepts this lower density directly, together with the actual bounded lengths; no replacement of these projected shadings is required.

All constants and maps have the intended dependence: the population constant is fixed globally, and the fiber constant depends only on the original fixed width and dimensions because c=1/4,K=20 are fixed. Empty original and selected families are included. Both original and target cells use the same delta; later common length normalization is part of the separate five-dimensional analytic adapter.

## Verification

Clean .olean build with zero diagnostics. The exact-source **production all-local audit** passed 24 theorem entries and 42 total local declarations, including generated record projections and instances. The only axioms are standard foundations: `propext`, `Classical.choice`, and `Quot.sound`. Source hash was checked again after the audit.

Evidence: `GaussianProjectedFamily_operator_audit.json`, `GaussianProjectedFamily_operator_audit.log`, and generated exact-source `formalization/GaussianProjectedFamily_OperatorAudit.lean`. No frozen381 source or shared registry was changed.

Independent reviews of the input geometry and seed are saved separately as `projected_grid_finite_review.md` and `five_dimensional_length_seed_finite_review.md`. The remaining step for this original Gaussian proof route is the analytic five-dimensional seed application and final scalar/log absorption; root owns that final assembly.
