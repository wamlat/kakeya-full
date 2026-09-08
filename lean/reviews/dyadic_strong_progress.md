# Strong moment interpolation on actual finite dyadic inputs

DyadicStrong.lean is frozen, clean-built, and exact-source audited with only standard Lean foundations. The audit JSON records final declaration counts and source hash.

The main theorem dyadic_strong_moment starts with elementary PositiveLaws for an actual operator T, a finite family of pairwise disjoint measurable sets E_j, measurable output T(f), and the restricted weak estimate only on the individual indicators E_j. Here f=Σ_j 2^j 1_Ej is the actual constructed finite input. For a>0,γ>0 and b=a(1+γ)<r it proves:

∫(Tf)^r ≤ 2^r r [A(1−2^(−γ))^(−a)/(r−b)] ∫f^r.

All integrals and inequalities are ENNReal; infinite band measures or output values cause no missing case. The constant is independent of the number and location of bands, sets, threshold, or function. The exact disjoint-band input moment identity is proved, rather than supplied as an assumption. The output measurability requirement is explicit and the actual Kakeya operator has a separate proved adapter for it.

The proof combines the previously proved concrete dyadic cutoff/geometric-weight distribution, the exact PowerKernel integral, finite sum integration, and the general ENNRealLayerCake theorem. It applies layer cake to Tf/2; the outer 2^r factor is proved by the actual scaling identity. The auxiliary integrate_band_distribution accepts precisely the distribution majorant that is independently constructed in RestrictedDyadic; the final theorem supplies it internally and has no distribution or energy oracle.

Choosing γ=(r−a)/(2a) yields every fixed r>a. The actual monotone extension to arbitrary measurable inputs, including infinite values, is constructed in DyadicApproximation/DyadicOperatorExtension and is being composed into RestrictedStrong by the finite-formal agent. The later strong L1/Lr-to-La interpolation remains a separate stage. This finite module itself does not yet assert the final maximal operator norm of the manuscript.

Reproduce with lake env lean -o .lake/build/lib/lean/DyadicStrong.olean DyadicStrong.lean and lake env lean ../dyadic_strong_axioms.lean. Files dyadic_strong_axioms.log and dyadic_strong_audit.json record the exact-source audit.
