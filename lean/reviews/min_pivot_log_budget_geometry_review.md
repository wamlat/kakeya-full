# Separate statement review: the minimum pivot logarithm

Read-only review of `formalization/MinPivotLogBudget.lean`, SHA256 `a80c585e5f7be68da70e8e27f78d6cfdbc0a5973d697a40cf192050c69c4e8e8`. No source edits or new axioms; the parent owns compilation and dependency auditing.

No mathematical or quantifier defect found. `minimum_lower` bounds each of the three terms in the actual minimum using the same factor `L^(-A max(1,1/alpha))`. Its assumptions `alpha>0`, `A>=0`, and `L>=1` are exactly the ones needed for the exponent comparisons. The positive fixed prefactor is `c*min(theta0,1/100,(c/B0)^(1/alpha))` and contains no actual A, B, theta or L.

The concentration calculation is an identity with positive bases: `(c/(B0 L^A))^(1/alpha) = (c/B0)^(1/alpha) L^(-A/alpha)`. Nothing is pulled out of the `1/alpha` power as an alpha-uniform constant. `source_lower` specializes the original source minimum; `normalized_lower` preserves the actual marked-normalization coefficient inside the small constant, so it also applies to the newly constructed marked-grid/length choice.

`source_notation` explicitly chooses its positive coefficient before A, B, theta and N. `source_log_ge_one` proves the necessary logarithm domain from N>=2. The result therefore closes the precise unnumbered logarithmic inequality in source §5.8 (PDF page 24), including its independence from the logarithmic budget A. Constants may depend on the fixed alpha, B0, theta0 and geometric normalization, as the source allows. It does not assert this same formula on arbitrary `0<L<1`.

This does not establish a comparison between two differently chosen geometric constants in kappa uniformly as alpha approaches zero. That separate distinction remains explicit in the final source-scope review.
