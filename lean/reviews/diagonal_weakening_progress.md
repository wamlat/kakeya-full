# Simultaneous diagonal weakening

`DiagonalWeakening.lean` is frozen and clean-built. Its three source theorems and five local theorem declarations passed the complete-source standard-foundations audit. SHA-256: `4231dbdecbaa784e3ff7bc14adb93c6c10128ac0cc96cce1996fd348f6321860`.

`DiagonalDiscreteEstimate.weaken` proves that the actual diagonal estimate at D implies the estimate at any d≤D. This is not justified by monotonicity of the density power alone. For every nonempty actual configuration, integer shading cardinalities imply delta≤2 lambda. The ratio of the desired scale-density term to the proved term is `(delta/lambda)^(D−d)`, at most `2^(D−d)`. Dividing the uniform constant by that fixed factor proves the conclusion. The empty family is handled separately. All constants are chosen before the actual configuration.

The two corollaries give diagonal 29/7 in dimension six and 37/7 in dimension eight from the now-proved stronger real-cap endpoints. The exponent comparisons use the existing kernel-proved rational bounds on sqrt(2). Subsequent measurable conversion handles arbitrary small measurable densities by its already proved occupancy and tiny-density branches.

Evidence: `diagonal_weakening_axioms.lean`, `diagonal_weakening_axioms.log`, `diagonal_weakening_audit.json`, and `diagonal_weakening_independent_review.md` (no defect found).
