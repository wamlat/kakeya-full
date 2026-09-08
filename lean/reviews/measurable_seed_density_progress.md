# Continuous source density and length coverage

Status: final sources compile with no diagnostics and pass the unchanged full-source theorem/declaration auditor. They await inclusion in the next frozen full-package checkpoint.

`DensityLogNormalization.lean` proves the fixed normalization coefficients for every L >= log(2), including L < 1. The positive lower density factor is bounded by c0, 1 and log(2)^ell. The normalized full-two-ends coefficient max(1, D L^t) has a fixed coefficient times L^t. Exact power identities account for both density losses.

`MeasurableSeedDensity.lean` proves source (4.4) for arbitrary measurable original unit-tube shadings with fixed physical widths and separation, independent logarithmic upper and lower density losses, every m > 1, and original full-shading physical two-ends estimates. It constructs actual radial measurable subsets of equal measure; original directions, cap coefficient, scale and union are preserved. No position bound is supplied. The conclusion retains the square-root inverse-cap factor.

`MeasurableSeedDensityLengths.lean` proves the same two public theorems for actual variable tube axes whose lengths are bounded above by any fixed positive constant. A temporary larger carrier establishes finite measure for trimming only. The estimate itself is applied to subsets of the original variable-length carriers. No lower axis-length bound is needed.

The original density band is c0 L^(-ell) sigma delta^(n-1) <= volume(Y_i) <= C0 L^u sigma delta^(n-1), with fixed positive c0,C0 and nonnegative ell,u. The original two-ends coefficient is B0 L^b and need not itself be >= 1. All final constants precede the original scale, density, cap coefficient, tube count, family, and measurable sets. The exact normalization contributes 2 ell to the final logarithmic loss and b+u+ell to the normalized two-ends budget.

Validation: DensityLogNormalization audited 18 local declarations/16 theorem declarations. Each of the two continuous modules audited both public theorems. Dependencies contain only propext, Classical.choice and Quot.sound. Independent review: measurable_seed_density_geometry_review.md; its final source hashes match the audited files.

Final SHA256:
- DensityLogNormalization: d99a95c33e9d932b1394e31d7c409a2fb7387cdeae1b16769af45f348fd3bee1
- MeasurableSeedDensity: cf4f4c5ee3650e79b6c890d75cbf87d6620f238ccd7193e9f3a80b20059e4475
- MeasurableSeedDensityLengths: 2005fa25b02fbaa8d99e9cf70b39b616df178b4bf95f535186a0bf952a3b0f88
