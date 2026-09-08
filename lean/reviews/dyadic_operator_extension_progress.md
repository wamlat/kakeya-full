# Actual operator monotone extension

`DyadicOperatorExtension.lean` converts a uniform moment estimate on actual finite disjoint dyadic inputs into the estimate on every measurable nonnegative extended-real input for the literal Kakeya operator.

The explicit finite-stage predicate `FiniteMomentBound k delta r B` quantifies all finite integer index sets and all actual measurable pairwise disjoint sets. It asserts the moment estimate only for their literal `bandSum` with the previously fixed dyadicHeight. This is the exact analytical input to be supplied by scalar's finite dyadic restricted-weak interpolation theorem; it is not an assumed full strong estimate.

The main theorem `extend hdelta hr hfinite f hf` has actual ambient k+1, delta>0, r>0. It applies the finite-stage hypothesis to the constructed DyadicApproximation bands. Their masses are bounded by the input via pointwise monotonicity. The actual operator's proved monotonicity, finite homogeneity, and exact monotone-iSup law show that its output is bounded by twice the supremum of outputs on those approximations. The actual output measurability theorem and monotone convergence for rth powers then pass the finite moment estimate to the full input, with exactly coefficient 2^r*B.

All sets, operator laws, output measurability and limit compatibility are proved internally from frozen modules. Infinite input values and infinite integrals are included directly in ENNReal, without an extra AE-finiteness argument. No strong bound, generic operator-law oracle, or custom axiom is inserted. The only remaining analytic premise is the explicitly stated uniform finite-stage moment bound; the module does not itself claim to prove that finite-band interpolation estimate.

Clean .olean build on first attempt with zero diagnostics. Frozen SHA256 b81c818f6cda7957f27017f4363773b80789684de279f0f3a151a8f78d9e310e. Exact-source audit PASS4 named declarations (one definition,three theorems), standard foundations only. No sorry/custom axiom; source-prefix/hash and expected-name checks passed. Audit files/log/meta use DyadicOperatorExtension_full_source_audit.* in audit_work.
