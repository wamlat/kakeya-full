# Actual high-density estimate for every good angular/spatial box

`formalization/AngularBoxHighDensity.lean` is complete, clean-built, and frozen. It imports the frozen `AngularSpatialBudgets` and `AnisotropicHighDensity`; no shared source or registry was edited.

`construct` fixes the base/lift estimates, ambient dimension, physical normalization constants, original two-ends B and exponent alpha, broadness beta, scale loss eps, and coarse-complement exponent a>=1. It chooses one positive cutoff delta0<=1 and one positive constant c BEFORE the original family F, mesh/density/cap coefficient, angular Pieces P, refinement V, simultaneous actual Package U, and good spatial box q.

It then applies the high-density theorem to the SAME `U.output q`; it performs no new shading or output selection. All conditioning budget premises are discharged internally using the actual refinement:

- effectiveRatio >= effectiveCoefficient*log(2/delta_old)^(-1);
- box two ends <= endsCoefficient*log(2/delta_old)^1;
- box marked broadness <= broadCoefficient*log(2/delta_old)^2.

The source depth and retained marked mass supplied those bounds in AngularRefinementBudgets and AngularSpatialBudgets. There is no caller-supplied per-box Input, budget, broadness, cap, population, or old-support premise. `box_full_support` proves the old-support condition for the literal `refinedCells V width q`. All subsequent full shadings use the same normalizeBox map on those references.

The normalized cap coefficient is `capFactor(k+1,3,m)*A_original`, with capFactor>=1 proved from m>=0. Thus A_original>=1 gives the required output coefficient>=1. Dividing the fixed estimate constant by capFactor removes it from the stated right normalization; A in the result is the ORIGINAL cap coefficient.

The exact result in ambient k+2 is

`c*A_original^(-1)*(delta_old/tau)^(m-D+eps)*physicalDensity(V,width)^C*Mq <= card(refinedCells(V,width,q))`,

where D=(2m+3+d')/4, C=(p+2q+4)/4, physicalDensity=V.density/widthFactor(k+2,width)^(k+2), and Mq is the original number of tubes in this actual spatial box. It recovers the density and population BEFORE the anisotropic segment/color/density selection, through the previously proved joint mass retention. The newly selected output population is not substituted for Mq.

Original log>=1 is derived: tau<=1 gives delta_old<=delta_new; the selected cutoff also has delta_new<=2/exp(1). No original-log lower bound is exposed as an extra hypothesis.

Residual conditions are explicitly the local analytic inputs, m,d>=0, p>=1,q>=2,D<m+1, fixed B>=1, alpha,beta,eps>0,a>=1; positive original mesh and A_original>=1; and the actual branch tests delta_new<=delta0, delta_new^a<=delta_old, output density>=delta_new^(1/3). The theorem starts from the constructed actual Package and does not decide these branches, sum the estimates across boxes/groups, absorb physicalDensity back to original lambda, or remove two ends. Consequently it is the concrete high-density angular-box application, not an unrestricted pivot estimate.

Verification: Lean 4.33.1 clean `.olean` build, zero diagnostics. Fresh whole-source audit of the one theorem passes with exact source-prefix match and only propext, Classical.choice, Quot.sound. Audit files: `angular_box_high_density_full_source_audit.lean`, `.log`, and `angular_box_high_density_audit_manifest.json`. SHA-256: `1b3b1856296c368cd6336ac2e9a231174f6bad5515a9a8606bbe0189a6d3a512`.
