# Anisotropic sampling population retention

The new `AnisotropicSamplingRetention.lean` is a packaging and quantitative-retention adapter for the frozen `AnisotropicSamplingInput.construct`. It makes no additional tube, segment, color, density-class, or marked-set selection. The original common spatial-box hypothesis remains explicit in its constructor.

## Proved bounds

Write the ambient dimension as `k+1`, the new mesh as `δ′=δ/τ`, the original population as `M`, the final population as `N`, the original density as `λ`, and the final density as `λnew`. Let

- `e = η / (segmentCount(angular) * paletteSize(k, separationFactor(angular)))`;
- `D` be the actual measured density-class depth constructed upstream.

The adapter proves, from actual retained marked measure and actual full-shading upper bounds,

`λnew * N ≥ e * λ * M / (16 * (D+1))`.

Since the upstream construction proves `λnew ≤ λ` and `λ > 0`, it also proves

`N ≥ e * M / (16 * (D+1))`.

The density-times-population estimate is stronger for subsequent summation than multiplying the separate density and population lower bounds. Its proof uses `marks_i ⊆ full_i`, finiteness inherited from the actual tube carriers, `μ(full_i) ≤ 4 λnew δ′^k`, and the already constructed original-population marked budget. It cancels the strictly positive `δ′^k`. No population, overlap, energy, or expected-value bound is assumed.

## Actual output record

`Output` preserves the same actual family, full sets, marked sets, selected original-index injection, exact `δ′` separation, inherited real-cap bound, and exact transformed original-set support. It includes the literal `SamplingNormalizedMeans.Input` with `c₀=2`, `C₀=4`, together with:

- `0 < e ≤ 1` and `D+1 ≤ log(4/e)/log(2)+2`;
- `e λ / 4 ≤ λnew ≤ λ`;
- `xi = e / (4(D+1))`, with `xi ≤ 1`;
- `Bnew = B * (4/e)`;
- `Knew = broadFactor(angular,beta,K) * (8(D+1)/e)`;
- the two population estimates above;
- retained marked mass at least `e λ δ′^k M / (4(D+1))`;
- each final full set inside the normalized image of its SAME selected original full set;
- final full-union volume at most original full-union volume divided by `τ^k`.

The compact record does not erase the actual measurable sets or replace them with a numerical oracle. The upstream original full sets may already be restricted angular-group sets; their precise support is retained by this adapter. The constructor still requires a genuine common parallel box for the original bases; the separate actual spatial partition supplies that hypothesis.

## Verification and scope

The module has three theorems and one structure. It compiles with the pinned Lean/mathlib project. The exact-source axiom audit is recorded in `AnisotropicSamplingRetention_axioms.log`; the associated source-audit file begins with the exact module bytes. No custom axioms, `sorry`, or `admit` are introduced. The scalar agent's separate `AnisotropicSamplingBudgets` module converts these literal bounds to uniform logarithmic budgets; this adapter does not assume those budgets.

Source SHA-256: `7b81218726795dd4d7fc436be0cd39b227bfba543a49cf7f88c1fad69a2758be`.
