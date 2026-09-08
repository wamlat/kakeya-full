# Complete normalized and cumulative Gaussian projection seed

`GaussianNormalizedSeed.lean` is frozen, clean-compiled and exact-source audited PASS. SHA256: `f0a6b55ef0da354e7da2975a9e05a4b630c1dd3cdbb3c59c376f386d83186594`.

All five named source theorems and twelve local declarations passed the exact complete-source audit. Every dependency is standard-only; there are no custom axioms, sorry/admit/native_decide, warnings or errors. See `gaussian_normalized_seed_audit.json` and `GaussianNormalizedSeed_SourceAudit.log`.

The module completes the source's actual Gaussian seven-to-five projection route at arbitrary fixed original separation normalization. It invokes `GaussianProjectionSeed.original_rows`, whose proof constructs the actual Gaussian-selected projected five-dimensional family and applies the proved five-dimensional seed. It does NOT obtain its seven-dimensional seed from the direct ambient-seven FractionalSeed conclusion. The five-dimensional input itself is constructively proved, so no new Wolff axiom is required by this route.

`normalized_rows` fixes geom and epsilon before c and before every actual F, delta, lambda, A or M. From the original geom.separation*delta separation it constructs the actual full separation coloring with paletteSize(6,geom.separation), independent of the mesh and all data. It chooses an actual largest class, whose population is at least M/palette. Every selected original tube keeps its complete original shading, original base, direction and row lower-density condition. The original cap coefficient A is inherited unchanged. Its union is an actual subset of the original union.

Applying the Gaussian seed to this exact-delta-separated class and multiplying its actual population bound loses only the fixed reciprocal palette factor in c. Thus normalized_rows proves c*A^(-1)*delta^(1/2+epsilon)*lambda^(7/2)*M<=original_union_card for arbitrary positive lambda with only original row lower bound lambda/delta. No lambda<=1 or row upper-density assumption is needed in this stronger row theorem. Empty families are covered by the actual empty color classes and zero population inequalities; the palette is always strictly positive.

`discrete_seed` gives the literal DiscreteEstimate 7 4 (7/2) (7/2) by taking the lower half of the actual Comparable input. `cumulative_seed` applies the already proved actual arbitrary-shading cumulative adapter. `source_cumulative` first weakens the NORMALIZED density exponent to 7/2+epsilon, where density<=1 makes that valid, and only then applies the actual cumulative construction. It does not incorrectly weaken an arbitrary cumulative density s, which may exceed one. This yields exactly c*A^(-1)*delta^(1/2+epsilon)*s^(7/2+epsilon)*M<=original_union_card, including unequal and empty shadings and s=0.

`source_count` sets delta=1/N for every real N>=1 and constructs the actual CumulativeConfiguration using the original total-incidence premise s*N*M<=sum_i card(shade_i). It preserves all original families, labels, cap and geometric data, and proves the exact power identity delta^(1/2+epsilon)=N^(-1/2-epsilon). Its final conclusion is literal source (2.2), with the constant chosen before N,A,s,M,F and with no positive lower cutoff on s.

This module completes the Gaussian proof route's normalized and cumulative quantitative conclusion, rather than merely restating an equivalent result supplied by another seven-dimensional proof. Earlier modules separately construct the matrix, collision expectation, simultaneous realization, graph selection, actual projected grid, target lengths/carriers/density and logarithmic absorption. The fixed geometric separation adapter here changes only which original tubes are used, preserving their complete actual shadings and controlling the original union by inclusion.

Commands in `audit_work/formalization` with pinned matching Lean/mathlib:

```sh
lake env lean -o .lake/build/lib/lean/GaussianNormalizedSeed.olean GaussianNormalizedSeed.lean
python3 ../audit_gaussian_normalized_seed.py
```

The file remains outside the earlier frozen registry until the parent's next integrated checkpoint. Read-only review of the logarithmic closing algebra is saved in `gaussian_projection_algebra_scalar_review.md`; root and finite agents independently review the full assembly.
