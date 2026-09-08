# Actual anisotropic high-density application

Two modules compile and pass the exact-source, all-local-declaration audit using only standard Lean foundations.

- AnisotropicDensityPower.lean: 2 source theorems, 2 audited declarations; SHA256 28f96d9fe1efed1ac1f5716b8f0d4aca7557437757ef7217a71d1f017f696445.
- AnisotropicHighDensity.lean: 3 source theorems, 3 audited declarations; SHA256 8008f5dd53c283c76bd0601ef0daf2fc9445b1e49bb0414aa4059d4e13519c6a.

AnisotropicDensityPower.output_power uses the SAME actual Output and its measured joint density-population bound. For effective retention e >= e0 L^(-x), it proves

`((e0/4)^(C-1) * e0/(16*depthCoefficient e0 x)) * L^(-(x*C+1)) * lambdaOld^C * MOld <= densityNew^C * NNew`.

This avoids multiplying two separate mass-retention losses. It requires C>=1, uses the actual selected depth bound, and changes no selected family or set.

AnisotropicHighDensity.original_parameters chooses a positive mesh threshold and coefficient BEFORE every original family, set, scale, density, cap coefficient and Output. It derives all literal xi/B/K budgets using AnisotropicSamplingBudgets, applies SamplingOriginalCells to the same output, recovers original lambdaOld^C*MOld using the power bound, and absorbs the logarithmic loss into eps/2. The resulting conclusion is

`c A^-1 (delta/tau)^(m-D+eps) lambdaOld^C MOld <= #old S`.

Every original Full set must lie in the common fixed width-normalized old cell union S. Output.contained constructs the exact pieceMap support; no sampled-cell overlap or volume identity is assumed. The cutoff is also at most 2/exp(1), so Lnew>=1 is proved internally.

original_log_parameters permits all conditioning budgets at the ORIGINAL logarithm. The actual coarse-range complement `(delta/tau)^a <= delta`, a>=1, transports these with fixed factors a^(-x), a^b and a^k. These factors are selected before scales. The high-density hypothesis remains on the actual selected output, and its analytic base/lift inputs remain explicit in this generic theorem.

The overall angular assembly, coarse/low-density alternatives, source-refinement budget integration and full two-ends removal are not claimed by these modules. Independent review and full checkpoint integration follow separately.
