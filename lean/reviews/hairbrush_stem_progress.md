# Actual stem incidence and bristle count

`HairbrushStem.lean` has 5 theorems and 2 definitions. It integrates an actual pointwise finite incidence count over an actual measurable portion S of a stem. Each transverse bristle intersection is bounded by the proved two-tube volume theorem. This proves the actual bristle cardinality lower bound `#H ≥ μ λ θ/(C_d δ L)` from volume(S)≥λδ^(d−1)/L and actual incidence multiplicity≥μ on S.

The final theorem `stem_hairbrush_union_lower` constructs actual common crossing points in S∩Y_T, performs measured two-ends removal, then uses actual planes, projective packing and measurable L2. The result is precisely the fine-scale structural estimate (4.15), with explicit dimensional constants:

`μ λ³ θ δ^(d−2) (rθ)^(d−2)/(C_d L⁴) ≤ volume(⋃ Y_T)`.

Remaining upstream assumptions are actual stem selection, a measurable S carrying the indicated mass and pointwise transverse incidence, and the original two-ends tests. These are meaningful geometric/combinatorial inputs, not the desired count or union inequality. A subsequent selection module is being developed to construct the stem from marked multiplicity levels and angular broadness.

The final theorem audit reports only standard axioms. No custom axioms or `sorry`.
