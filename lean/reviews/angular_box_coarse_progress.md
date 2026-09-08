# Actual coarse branches for the same angular/spatial boxes

`formalization/AngularBoxCoarse.lean` is complete, clean-built, and frozen. It imports the frozen `AngularSpatialSampling` and `LocalAngularCoarse`; no shared source or registry was edited.

The two public branch theorems quantify their positive constants BEFORE F, the angular Pieces P, the actual refinement V, the simultaneous Package U, and the actual good box q. Both use exactly `boxFamily V width q`, whose old finite shadings are comparable at V.density and whose finite union is literally `refinedCells V width q`.

`box_geometry` derives the old cap condition and local direction cap of radius 3*tau from original g-membership, separation, bounded bases and cap geometry. The fixed radius is nonnegative. There is no caller-supplied population estimate, occupied-cell estimate, or local-cap oracle. The underlying LocalAngularCoarse theorems derive population from the complete cap condition, including their large-cap radius-one covering case, and obtain the union lower bound from one actual old shading.

V.density need not be at most one. `original_density_le_two` uses the actual bound V.density<=2*originalLambda with originalLambda<=1. Both branches therefore use lamMax=2 and pay the explicit fixed factor 2^(1-C). `physical_density_le` proves V.density/W^ambient<=V.density from W>=1. `density_target_le` uses C>=1 to weaken the desired bound to this physical density, matching the exact target of AngularBoxHighDensity.

For ambient k+2, the fixed cap-population coefficient is

`Kpop = LocalAngularCoarse.populationCoefficient(k+1,3,m)`.

`coarse` takes m>=0, D<m+1, m+1<=ambient, C>=1, eps>=0 and the branch condition

`delta_old^(1/(2*ambient)) <= delta_old/tau`.

Its fixed coefficient is `2^(1-C)/Kpop`. `bounded_scale` takes m>=0, C>=1 and a fixed delta0>0, with branch condition `delta0 <= delta_old/tau`. Its coefficient is `2^(1-C)/(Kpop*max(1,delta0^(-D+eps)))`; this branch does not require a D or eps sign restriction.

Both conclude precisely

`c*A_original^(-1)*(delta_old/tau)^(m-D+eps)*physicalDensity(V,width)^C*Mq <= card(refinedCells(V,width,q))`.

The proof handles the whole actual box family; it does not replace Mq by the later anisotropic output population. U is accepted to keep the same dependent good-box interface as the high/low applications, but the elementary proof is stronger: it does not use U's chosen output, sampling input, or analytic estimates at all. Original separation/location hypotheses are used only through the existing checked box_geometry adapter; the count itself ultimately uses cap/local direction geometry and actual comparable old shadings.

Scope: these are the coarse normalized-scale and fixed-large normalized-scale cases, ready to combine with high/low density estimates. The module does not choose branches, prove the generalized pivot or sum angular pieces. All constants are uniform in actual meshes, scales, densities, populations and cap coefficients.

Verification: Lean 4.33.1 clean `.olean` build, zero diagnostics. Fresh whole-source audit of all five theorems passes with exact source-prefix match and only propext, Classical.choice, Quot.sound. Audit files: `angular_box_coarse_full_source_audit.lean`, `.log`, `angular_box_coarse_audit_manifest.json`. SHA-256: `a0946ccf909eaf83e0affb470b541a871566e8acf7c292c5207f35f939c910e9`.
