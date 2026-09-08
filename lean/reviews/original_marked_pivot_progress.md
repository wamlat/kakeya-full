# Complete original marked fourth-power core — checkpoint 12

`OriginalMarkedPivot.construct` now constructs the complete Section 5 core from the original finite marked tube family and two analytic inputs: DiscreteEstimate in ambient k+2 with parameters m,d,p, and the lifted estimate in k+3 with parameters d,d',q. It assumes m,d>=0, p>=1, q>=2, fixed width>=1/12 and bounded base radius. The original geometric hypotheses include positive comparable full shadings, actual marks contained in them, marked mass, pointwise angular broadness, all-radius full two ends, cap bounds, actual separation/admissibility, and a finite original covering set E. Scale and final positive constant are chosen before all configuration variables.

No selected output data, normalized family, retention inequality, raw fourth-power bound or collision-energy estimate is supplied by the caller. OriginalPivotSlabs constructs the actual pruned/recovered configuration and selected slabs. SelectedBaseFamilies and SelectedColoredFamilies construct the actual normalized families and fixed colors. SelectedFamilyPruning applies the lifted estimate to construct retained incidences. ConstructedPivotClosing attaches actual selected original endpoint witnesses and proves their closing inequality. OriginalPivotEnergy transfers it to the original covering set. OriginalPivotScalar combines it with the actual base estimate.

Writing L=pivotLog(delta), sigma for the constructed dyadic fiber parameter, and kappa for the explicit product choice, the final fourth-power theorem is

    c kappa^[5(k+1)+6q+12] A^-1 xi^(p+3) L^[-(p+4)]
      delta^(-2m-3-d'+3e) lambda^(p+2q+4+2e) (M delta^m)^3 <= |E|^4.

Here 0<e<=1, 0<lambda,xi<=1. Fixed bounds B<=B0 log(2/delta)^b and theta^-1<=K0 log(2/delta)^qLog are explicit, and the constants can depend on their fixed parameters and positive two-ends exponent alpha. No uniformity as alpha tends to zero is asserted. The larger logarithmic losses from the product parameter are covered by PivotLossAbsorption. That module derives lambda>=delta/2 and M delta^m<=C A from actual configurations, absorbs fixed logarithms and the small density error, and proves the exact root exponents D=(2m+3+d')/4 and C=(p+2q+4)/4 with a linear inverse-A final bound from an appropriate raw fourth-power estimate.

## Exact source boundary

The product kappa used here is not uniformly comparable from below to the manuscript's literal minimum choice. MinPivotKappa proves both the admissibility of a manuscript-form minimum and an explicit noncomparability counterexample. The fourth-power theorem above therefore does not silently assert the literal minimum-kappa quantitative Theorem 5.1. Its fixed-log-budget endpoint consequence remains valid. See pivot_kappa_convention_review.md.

The main unrestricted pivot still needs actual sampling/angular conditioning and removal of original full two ends. The main Kakeya theorem and final maximal-operator deduction remain unproved. Later development must not be confused with the exact checkpoint manifest.

## Verification

Each module compiled locally without diagnostics and passed a complete-source Lean environment axiom audit, including generated theorem declarations. The full frozen package build and repeated audits are recorded in checkpoint 12's verification/summary.json after they pass. An independent statement review of the original marked composition found no defect; see original_marked_pivot_independent_review.md. Standard foundations only; no custom axioms, sorry, admit or native_decide.
