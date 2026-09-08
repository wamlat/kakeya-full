# Separate geometry review of exact whole-sphere test counts

Read the complete frozen `SphereNetExactBudget.lean` at SHA `3962cc9ebd618e80efd01e0cca1a553d299550a41f530bb3418932e21220df52`. No mathematical or quantifier-order defect was found. No recompilation or source edits were performed for this read-only review.

`linear_count_budget` uses the actual full-sphere net packing bound and a proved uniform logarithmic-power estimate to derive `net.card <= H*N`. The constant `H` depends only on the fixed dimension and inverse-radius budget. It is positive and chosen before the actual radius, net and scale. The result handles dimension parameter zero and logarithmic power zero without replacing the ambient-minus-one exponent by the ambient exponent.

`exists_product_threshold` absorbs the fixed positive spatial prefactor `P` into `max 1 (P*H)`, so the literal product test count is at most `N^(D+2)` with coefficient one. It does not drop `P` or assume a count of the net. The exponent `D` is an arbitrary real parameter introduced after the threshold; this stronger uniformity is valid because its only subsequent use is multiplication by the positive quantity `N^D`.

`exists_augmented_threshold` retains the additional high-cell lower-tail test. It proves `1+net.card <= (1+H)*N` for `N>=1`, absorbs `P*(1+H)` into the threshold, and obtains `S.card*(1+net.card) <= N^(D+2)`. This is the actual number needed for the simultaneous cell-lower and cap-upper events. No assumption that the net is nonempty is necessary for that `+1` argument.

The hypotheses on the actual spatial count and inverse radius remain explicit numerical interfaces; the geometric sampling application must supply them from its original support and theta choice. This is consistent with `SphereNetSourceFailure`, which constructs precisely those inputs from the original measurable data. The independent in-module count proof there reaches the same ambient specialization.

No source, shared registry, verifier or published checkpoint was modified.
