# Closing actual selected-output energy at the original mesh

`SelectedOutputClosing.lean` composes the actual selected-output witness energy with the exact retained mass and upper degree energy supplied by grouped analytic pruning. Its objects are the original selected output P, simultaneous actual LineData D, original-output color and normalized shading maps, and the actual retained set T contained in the literal grouped incidences.

The hypotheses retain the specific shifted-selected-cell containment and at least K/3 normalized cells per output. From these the earlier actual constructions derive rho>0, Q>0, original endpoint occupancy and the lower energy. No geometric witness, energy lower bound or abstract sample map is supplied.

The closing argument uses delta_n=delta/R and kappa_n=kappa/R, where R=1+2width. The new exact normalization identity returns to the original variables before applying source output-count formulas. If t=d-d'+1+epsilon, the fixed coefficient is

    c_original = c_close / R^(5+t) > 0,

and the result is

    c_original kappa^5 A^-1 rho^r delta^t Q ≤ |F.unionCells|².

The exponent t may have either sign. Positivity of R makes the normalization cost legitimate in all cases. The stronger kappa^5 gain can later be weakened to kappa^6 when kappa≤1; the code does not silently mix normalized kappa with the original output count.

The explicit remaining analytic inputs are precisely T subset S, |T|≥|S|/2 and the grouped upper degree energy, with the same rho=delta_n|S|/Q and same fixed color-count factor J. A complete pivot construction must instantiate these with its actual normalized colored family and uniform analytic constant, then compose the original output population, cutoff, logarithmic losses and coarse-scale branch.

All three source theorems clean-build and pass a fresh full-source environment audit, including generated declarations, with only standard foundations and no diagnostics. This module is later development than frozen checkpoint11 and awaits its next full-package checkpoint.

Local theorem declarations audited: 19. Source SHA-256: `685080cb4210d32bd00cd1f375be92ecb9e75b8b2616a4eae540bb024d17a0cc`.
