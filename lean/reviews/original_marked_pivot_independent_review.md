# Independent audit: OriginalPivotScalar and OriginalMarkedPivot

Verdict: PASS for the precise stated product-kappa, logarithmic-budget, small-scale marked fourth-power theorem. No substantive defect or premise laundering was found. The main theorem constructs the package and actual closing energy internally from the two explicit finite DiscreteEstimate hypotheses. It does not claim the unrestricted pivot implication or literal equivalence with the manuscript's minimum-kappa theorem.

## Source and kernel audit

Read both target modules in full, against OriginalPivotSlabs.Package, OriginalPivotEnergy.construct, PivotFourthPower, the density/closing lemmas in ClosingEnergyAlgebra, Configurations.DiscreteEstimate, Endpoint.weaken_density, and the actual cumulative extension. Compared the statements and substitutions with combined PDF sections 5.1–5.7, especially equations (5.3), (5.6), (5.10), (5.19), (5.22), (5.33) and (5.34).

A fresh audit source copied the full bodies of BOTH modules, imported only their external dependencies, and printed the axiom sets of all five local definitions/theorems. It compiled without errors or warnings. Each declaration depends exactly on `propext`, `Classical.choice`, and `Quot.sound`. There is no sorry, admit, unsafe declaration, custom axiom or imported opaque substitute for either target proof.

Audit source/log: `original_marked_pivot_independent_audit.lean` and `.log`.
Final verified source hashes, checked again after compilation:

- OriginalPivotScalar: c87adba70776c9b7e5379148e973deeb3af97f47a8bcce2da56b22739074ec6f
- OriginalMarkedPivot: d2c94ef5cbb39e1d8949b7040442cad3d4d803a3c1edf01dba6607abeb085bcb

## 1. Proxy angle mass is an exact algebraic rewrite

The local variable named `angles` is defined as

    angleProxy = xi^2 lambda^2 M^2 / (delta^2 |E|).

It is not asserted to be the cardinality of an actual angle set or a unit-constant lower bound for that cardinality. The package ALREADY proves the original-parameter actual-output inequality

    Q >= (outputCoefficient/65536) kappa^(5(k+1))
         xi^2 lambda^8 M^2 / (sigma^2 delta^4 pivotLog^3 |E|).

Consequently rewriting its numerator as lambda^6*angleProxy is exactly valid. The proof checks this identity by field/ring normalization. Passing `ca=1` and the tautological inequality angleProxy<=angleProxy into the generic fourth-power algebra is therefore correct. It is not a fresh assertion that the actual angle count has unit lower constant, and it does not erase a factor 1/128. Actual marked-angle and recovery constants were already included in 1/65536 upstream. For prose explanations, calling this an angle proxy avoids confusing it with a finite set cardinality.

## 2. Original lambda, sigma constant and coefficient

The original density remains lambda throughout. The recovered family may have density lambda/2, but the package explicitly accounts for it. The sigma lower bound is

    sigma > lambda^2 / (2048*outputConstant).

The scalar coefficient uses exactly cS=1/(2048*outputConstant). It converts the strict package inequality to a weak inequality and raises it only to q+eps-2>=0, using q>=2 and eps>=0. There is no replacement by the stronger pre-recovery denominator 512.

The actual density lower bound is rho>=cR*kappa^6*sigma, with cR=SelectedOutputDensity.lowerCoefficient(k+1,width). This coefficient already includes unit-segment factor three, normalized mesh and normalized-kappa factors. No additional factor three is lost or restored in the scalar proof.

The combined density factor before the angle-proxy substitution is

    lambda^6 * sigma^(q+eps-2)
      >= cS^(q+eps-2) * lambda^(2q+2+2eps).

The angle proxy contributes another lambda^2, and the inverse spatial cutoff contributes lambda^p. The final density power is exactly p+2q+4+2eps.

The final coefficient is

    cClose*(outputCoefficient/65536)*cR^(q+eps)*cS^(q+eps-2)
      / [(K+1/cBase)*100^(p+1)],

which is positive under the displayed fixed-parameter hypotheses.

## 3. The literal maximum cutoff is controlled, not dropped

Let

    Y = |E| A delta^(d-m-eps) lambda^(-p) / M,
    eta = xi / [100(J+1)].

The original base estimate gives Y>=cBase. Since 0<xi<=1, J>=0 and p>=1, one has 0<eta<=1 and eta^(-(p+1))>=1. The proof therefore obtains

    max(1, K Y eta^(-(p+1)))
      <= (K+1/cBase) Y eta^(-(p+1)).

Thus the unit branch is paid by the explicit 1/cBase term, even if K is small. It is not assumed that the untruncated expression is already at least one, and no configuration-dependent enlargement of K is made.

The exact marked-budget identity contributes 100^(p+1), xi^(-(p+1)) and (J+1)^(p+1). The package depth estimate implies J+1<=pivotLog(delta). With delta<=1 and eps>=0 the actual delta^(d-m-eps) is bounded above by delta^(d-m-2eps), an explicit additional weakening. This produces the source-form cutoff with two eps scale losses.

## 4. Kappa exponent and dimension convention

The actual energy theorem gives a kappa^5 gain. The scalar proof deliberately weakens it to kappa^6 using 0<kappa<=1. Combining output population kappa^(5(k+1)), density kappa^(6(q+eps)) and this gain yields

    kappa^(5(k+1)+6(q+eps)+6).

For eps<=1, the exponent 5(k+1)+6q+12 is at least that value. Since kappa<=1, replacing the former power by the latter weakens the lower bound in the correct direction.

Here original physical ambient dimension is n=k+2, so projective direction dimension is k+1=n-1. Thus the exponent is exactly the source's 5(n-1)+6q+12. The lifted DiscreteEstimate is in physical dimension k+3=n+1. No off-by-one substitution appears.

## 5. Original cap coefficient, population and scale powers

The proof never replaces original M by the number of recovered tubes. M occurs in the package output estimate, in the actual original cutoff, and in the original base configuration.

The final inverse original cap coefficient is explicitly A^(-1). It comes from the inverse original cutoff. The graph/cell geometry factors have already been absorbed into cClose independently of A and the configuration. The manuscript uses a fixed absolute cap constant, which can absorb A into its fixed coefficient; the formal theorem keeps this dependence visible.

The exponent calculation before writing S=M delta^m is

    (d-d'-1+eps) - (d-m-2eps) - 2
      = m-d'-3+3eps.

The three eps losses are therefore precisely two from the cutoff form and one from closing. Multiplying by original M^3 and rewriting gives

    delta^(m-d'-3+3eps) M^3
      = delta^(-2m-3-d'+3eps) (M delta^m)^3.

With N=delta^(-1), this is N^(2m+3+d'-3eps) S^3. The marked and logarithmic powers are respectively xi^(p+3) and pivotLog^(-(p+4)), matching the source up to the fixed convention for logarithms.

The two inverse factors of |E|, one from the cutoff and one from the angle proxy, are multiplied through the closing |E|^2 bound to obtain |E|^4. Positivity of the actual comparison cardinality is supplied by the recovered package; division by zero is not hidden.

## 6. Density weakening q to q+eps is valid for the actual cumulative use

OriginalMarkedPivot first invokes Endpoint.DiscreteEstimate.weaken_density on the normalized lifted DiscreteEstimate. That theorem only uses normalized configuration densities in (0,1], where lambda^(q+eps)<=lambda^q.

It then passes the resulting DiscreteEstimate with density exponent q+eps to OriginalPivotEnergy. The genuine finite cumulative extension is constructed AFTER this weakening, and its arbitrary-density normalization already accounts for fixed geometric upper density constants. The proof never asserts rho^(q+eps)<=rho^q for a possibly larger-than-one cumulative rho. This distinction avoids the common error in applying density monotonicity directly to the lifted cumulative density. It is consistent with the source's instruction to absorb fixed upper-density constants.

## 7. No scalar premise is left unproved in the main theorem

OriginalPivotScalar.fourth_power is intentionally a conditional numerical lemma. OriginalMarkedPivot.construct discharges every one of its substantive premises:

- Actual package, sample selection and slab data: OriginalPivotSlabs.construct from the original marked Hypotheses and base DiscreteEstimate.
- Actual rho and closing inequality: OriginalPivotEnergy.construct from the lifted DiscreteEstimate and that SAME package.
- Original base inequality: the base DiscreteEstimate is evaluated on a ShadedConfiguration containing the literal original F, delta, lambda, A and M. Its normalization has the original width, separation factor one, and radius max(1,baseRadius). Actual original boundedness supplies this enlargement.
- Comparison with E: the original cover hypothesis is used to prove F.unionCells subset E, then actual cardinality monotonicity gives the displayed original base bound.
- Positivity, depth and geometric tests: obtained from the original hypotheses/package, not assumed as desired analytic conclusions.

There is no assumed angle abundance, collision-energy estimate, lifted cap bound, color selection, retained-mass bound, endpoint support count or final fourth-power inequality in the main theorem's input. Its two DiscreteEstimate assumptions are the actual quantified finite tube/grid predicates defined in Configurations, not custom opaque placeholders.

## 8. Uniformity and residual scope

The pruning K and scale threshold are chosen from fixed parameters before the later configuration. The original base coefficient is chosen at a fixed normalization before delta, lambda, A or M; the closing coefficient is chosen before K and the package/configuration. The final delta0 and c therefore precede F,E,marks,M,delta,A,lambda,xi,B,theta. They may depend on the stated fixed dimensions/exponents, width/bounded-region normalization, alpha and the fixed logarithmic-budget data. No later concentration coefficient is captured in a supposedly uniform constant.

Important exact scope limits remain:

1. Kappa is the explicitly proved PRODUCT choice using recovered coefficient 2B, not the manuscript's minimum choice. Its positivity/tests are proved, but no equivalence with the minimum choice is asserted. The ratio can depend on B and theta; replacing it by the minimum without a separate proof would strengthen the theorem unjustifiably.
2. The theorem is the small-scale branch under fixed quantitative polylogarithmic upper bounds on B and theta^(-1). It is not the full source formulation for arbitrary B,theta under only N*kappa_min^20 sufficiently large. No lower logarithmic bound on xi is required for this fourth-power statement.
3. The actual original shadings have comparable full density with 0<lambda<=1 and 0<xi<=1; fixed-theta marked broadness and full two-ends remain original assumptions. Alpha is fixed positive. Width>=1/12 and the chosen exact separation/comparability normalization are explicit.
4. The formal base construction requires p>=1, whereas the source's broad statement lists p>0. The recursive range p>=d>3 satisfies the formal requirement. The theorem does not purport to cover the entire p in (0,1) portion of that source statement.
5. The two base/lifted analytic estimates remain hypotheses. This proves their marked transverse pivot consequence on actual configurations, not those estimates from nothing.
6. Removing broadness and two-ends, deriving the logarithmic conditioning budgets, covering scales above delta0, obtaining the unrestricted RealCapEstimate pivot implication, and completing the endpoint recurrence remain separate tasks. The source's population upper bound needed later for S^(3/4) to S is not used or assumed in this fourth-power theorem.

These limitations are visible in the current statement and documentation. They do not invalidate the proved marked product-kappa consequence.
