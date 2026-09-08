# Actual sampled family to the marked pivot

SamplingPivotInterface constructs the literal OriginalPivotSlabs.Hypotheses record for SamplingRealization.full and its original-label marks. It proves the marked-mass conversion, exact factor-two density, original cap/separation/base inheritance, geometric admissibility, support containment, pointwise broadness, all-radius full two ends and transformed logarithmic budgets.

The input outcome must have the narrow [2mu/3,4mu/3] full-count band with mu=cEq*lambda/delta. The ordinary wider SampleGood band is not silently treated as Comparable. Full and marked cells come from that same outcome, with no tube binning. Normalized total marked expectation is bounded below by (1/R)*xi*lambda*M/delta, with R>=1 and 0<cEq<=1. The resulting density is (2/3)*cEq*lambda and safe marked fraction xi/(8R), both positive and at most one. The factor xi/(8R) retains a fixed logarithmic lower bound. All-radius two ends uses the explicit factor 2*4^alpha*C, also transferred to its fixed logarithmic coefficient.

SampledMarkedEstimate then applies the actual all-scales marked pivot theorem. Its positive constant precedes every tube family, support, probability array and outcome. It absorbs only the fixed density factor ((2/3)*cEq)^C and concludes the bound in the ORIGINAL lambda and delta:

    c A^-1 delta^(m-D+epsilon) lambda^C M <= |E|,
    D=(2m+3+d')/4, C=(p+2q+4)/4.

The two discrete estimates, original geometry and conditioning budgets, and actual coupled sampling outcome remain explicit inputs at this interface. The constructive sampling theorem supplies the outcome; its full composition from original measurable shadings remains the next step. This is not yet an unrestricted pivot theorem and is not a proof of the main Kakeya theorem.

Verification: clean builds and complete-source Lean environment audits, standard foundations only, no custom axioms or placeholders. These modules belong to development after checkpoint 13 until frozen and fully verified in a later manifest.

SamplingPivotInterface: 7 local theorem declarations, SHA-256 15a4809b72d7e67985bb115e82be8094644adb93e30e087da8a795b121943ca0.
SampledMarkedEstimate: 1 local theorem declarations, SHA-256 74adacfc34c19873d9fee1bc66c5261e02ae1b980e377ef8d216972f9589a16f.
