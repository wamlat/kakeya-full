# Separate six-dimensional marked-core review

Read-only mathematical review of `SixDimensionalCore.lean` found no substantive defect. This review did not duplicate the author's compiler or axiom audit.

The seed specialization uses actual ambient dimension6 and real-cap parameter5, hence both seed exponents(5+3)/2=4. The lift is in actual ambient dimension7, with real-cap parameter4, hence both lift exponents(4+3)/2=7/2. These match `MarkedPivotEstimate.all_scales` with k=4, m=5, d=p=4, d'=q=7/2.

The exact formulas give D=(2*5+3+7/2)/4=33/8 and C=(4+2*(7/2)+4)/4=15/4. Thus the original discrete occupied-cell exponent is m-D=7/8. The epsilon sign is positive, and the original cap coefficient occurs as A^-1. The covering-set version and literal full-union version keep the same full family and marked subsets.

The positive coefficient is quantified before the family, population, covering cells, marks, scale, density, A, xi, B and theta. It may depend on the explicitly fixed geometry, error, two-ends exponent and conditioning budgets. The theorem still requires the full `OriginalPivotSlabs.Hypotheses` record, lambda<=1, xi<=1 and the stated lower logarithmic marked-fraction budget. It is correctly labeled a marked/two-ends conditioned core; it does not assert an unrestricted M6 endpoint or a general measurable Kakeya bound. No Katz–Tao axiom is invoked by this source: both named analytic inputs are the proved fractional seeds.

Reviewed source SHA-256: `b37e9ee19d97d10e487534d25df89c00d5f71432b0fb5e1b4599d7cdc19c4db7`.
