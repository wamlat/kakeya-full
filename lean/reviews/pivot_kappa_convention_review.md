# Pivot-scale convention: exact statement boundary and a proved minimum choice

The manuscript's physical PDF page 17, immediately before Theorem 5.1, defines

`kappa_src = c_k min{theta, 1/100, (c_k/B)^(1/alpha)}`.

The quantitative bound (5.3) uses `kappa_src^H`, with `H=5(k−1)+6q+12`, and constants independent of B and theta. The physical page 6 six-dimensional specialization repeats this convention and exponent 58. These are stronger parameter-specific claims than a bound with an arbitrarily smaller legal radius.

## What the current constructed package actually chooses

The frozen `OriginalPivotSlabs.kappa` is literally

`PivotKappa.choice width (2B) theta^(-1) alpha 1`.

Writing D=2width+1, its exact value is

`kappa_prod = theta (32B)^(-1/alpha)/(200D)`.

The factor 2B is the actual deterioration of two ends after pruning/recovery. The fixed-radius marked broadness input is only the manuscript's one cap radius theta; the package does not require a stronger all-scale angular power law. `MarkedSubsetSamples.fixed_radius_choice` uses coefficient theta^(-1) and exponent one purely to construct a suitable scalar radius.

This radius is legal, but it is not uniformly comparable from below with the source minimum. This is now itself machine checked in `MinPivotKappa.no_uniform_product_lower`, at fixed physical width 1/2 and fixed alpha=1. For every t≥1, take B=t and theta=1/t. With the permitted fixed source constant c=1/200, the file proves exactly

`kappa_prod = 1/(12800 t^2)`,

`kappa_src = 1/(40000 t)`.

Their ratio is `25/(8t)`, which tends to zero. The Lean theorem proves there exists no positive constant c, independent of t, with `c*kappa_src ≤ kappa_prod` for all these parameters. The width 1/2 lies inside the actual package's width≥1/12 normalization.

Consequently a lower bound involving `kappa_prod^H` does not, by a fixed-constant comparison, establish (5.3) with `kappa_src^H`. Likewise a cutoff based on `N*kappa_prod^20` is not the manuscript's cutoff based on the larger source radius. This identifies a formalization boundary; it does not refute the manuscript theorem. Its generic legal-radius geometric steps remain available for a new wrapper.

The package also fixes polynomial logarithmic budgets for B and theta^(-1) before choosing its scale threshold. Under those budgets, the product radius has a fixed polynomial logarithmic lower bound, independent of density. Thus this convention difference does not obstruct the intended endpoint implication after absorbing logarithms. It does matter to a claim that the exact quantitative Theorem 5.1, with its displayed kappa and H, has already been established.

## New complete scalar lemmas

`MinPivotKappa.lean` defines the actual largest nonnegative radius meeting the three scalar tests, with B now denoting the post-recovery coefficient:

`kappa_opt = min{1/100, theta/2, (16B)^(-1/alpha)/D}`.

For width≥0, B≥1, alpha>0 and theta>0, `optimal_admissible` proves positivity, kappa≤1/100, 2kappa≤theta, D*kappa≤1 and `B*(D*kappa)^alpha≤1/16`. `physical_test_iff` proves the exact equivalence between the power exclusion test and its explicit radius bound, and `maximal` proves that every nonnegative radius satisfying the three actual tests is at most this minimum. Maximality is derived from monotonicity of real powers, rather than assumed as a hypothesis.

`product_le_optimal` proves that the existing fixed-radius product choice is at most this maximal minimum. `optimal_log_lower` transfers the existing uniform polynomial logarithmic lower bound to it. Therefore a previously proved twentieth-power lower cutoff for the product also gives that lower cutoff for this larger optimal minimum by monotonicity; this is a scalar transfer, not a replacement of the frozen data definitions.

The file separately constructs a literal manuscript-form minimum with one fixed geometric constant used both outside and inside:

`c_w = 1/(100D)`,

`sourceChoice = c_w min{theta, 1/100, (c_w/B)^(1/alpha)}`.

Here B is the original coefficient. `source_admissible` proves all the same positivity/geometric tests and the exact post-recovery legal test

`(2B)*(D*sourceChoice)^alpha ≤ 1/16`.

These proofs require no upper bound alpha≤1; they hold for every alpha>0, with c_w independent of alpha, B, theta and density. Fixed width is part of the geometric normalization, so this has the manuscript's permitted constant dependence. `source_le_optimal` compares this source-form radius with the maximal admissible minimum for the actual coefficient 2B.

## Remaining integration

No frozen module was changed. The currently constructed `OriginalPivotSlabs.Package` still uses its exact product definition. To establish the displayed min-kappa quantitative theorem, a new original-input wrapper must use the minimum's proved scalar tests when constructing actual legal samples, selected fibers/slabs, and the final energy data. The existing generic actual-sample and geometry-scale theorems accept explicit radii/tests, so there is no new analytic inequality implicit in this scalar repair. The new wrapper must keep its scale condition in the literal source radius; it must not obtain that condition by reversing the proved one-sided comparison. This report does not claim that integration is complete.

## Verification

The module contains 17 theorems and three definitions. The module is clean-compiled, built, and frozen. A fresh audit of the full source plus all 20 named declarations passed with an exact source-prefix match, no errors or warnings, and axiom union exactly `propext`, `Classical.choice`, `Quot.sound`. No custom axioms, sorry, or admitted results have been introduced.
