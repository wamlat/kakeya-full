# Independent review of the actual cumulative bush proof

Root reviewed the complete source `Bush.lean` and its imported geometric interfaces after the geometry agent's proof, on 6 September 2026. This is a separate derivation/statement review within the same AI-assisted process, not independent human peer review.

No mathematical defect or hidden analytic-seed assumption was found.

The main estimate uses actual finite `TubeFamily` shading incidence, actual integer-grid centers, actual unit-axis tubes and the original `CapBound` predicate. It does not assume direction separation, a bush count, a total tube count or a bounded-region volume estimate. The assumptions m>0, δ∈(0,1], s∈(0,1], A≥1 and M>0 match the cumulative statement; individual zero shadings are allowed.

The geometric local constant is L=(6+4W)[2ceil(W+1)+3]^d for W≥1. With D=64WL, the dense condition Dδ≤s and r=s/(8L) give 8Wδ≤r≤1. Hence r≥δ, 4Wδ≤r and both allowed-cap tests δ≤8Wδ/r≤1 are proved, rather than assuming a cap estimate outside its stated radius range. Near-ball cells are bounded by Lr/δ=s/(8δ); retained tubes had at least s/(2δ) cells. The actual incidence double count therefore has a positive outside population and yields the stated square inequality with a conservative constant.

The sparse branch uses the separately proved finite cap cover M≤P Aδ^(−m), s≤Dδ, positive cumulative mass and the resulting actual E≥1. No density-dependent logarithm or assumed nonempty individual tube is introduced. The exponent m+2 is nonnegative because m>0.

Taking square roots uses positive/nonnegative quantities with both squared identities checked. A second use of the same actual total-count bound changes sqrt(M/A) to M/A with the correct δ^(m/2) factor. The final δ power is m/2−1 and density power is (m+2)/2. A is inverted once in the linear conclusion, as required for growing coefficients.

The quantified constant `bushConstant k (max width 1) m` is chosen before scale, density, cap coefficient, tube number and configurations. Width enlargement is proved. The DiscreteEstimate wrapper derives cumulative mass from actual comparable counts, weakens by δ^ε≤1, and separately handles M=0. The RealCapEstimate wrapper handles every adequate integer ambient dimension, ruling out the zero-dimensional case from m>0 and the ambient constraint.

This closes Appendix A.1 in the stated finite Euclidean model and provides an unconditional finite bush seed. It does not prove the stronger fractional hairbrush seed, the novel pivot transition, a measurable transfer by itself, or the final maximal estimate.
