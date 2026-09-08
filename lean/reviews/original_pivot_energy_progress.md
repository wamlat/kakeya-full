# OriginalPivotEnergy

Status: complete and frozen. The module compiles to its local `.olean` with no warnings. All three local theorem bodies were inspected and compiled from source with printed axiom sets exactly `propext`, `Classical.choice`, `Quot.sound`. No sorry, admit, custom axiom or unsafe declaration occurs. Log: `original_pivot_energy_compile.log`.

## Actual integration

For fixed width, original bound radius, d>=0, r>=1, eps>0 and lifted `DiscreteEstimate (k+3) d d' r`, `construct` chooses c>0 BEFORE K and all original families, comparison sets, marks and `OriginalPivotSlabs.Package` values U. It returns an existential rho satisfying

    rho > 0,
    rho >= SelectedOutputDensity.lowerCoefficient(k+1,width) * kappa^6 * sigma,
    c * kappa^5 * cutoff(U)^(-1) * rho^r
      * delta^(d-d'+1+eps) * Q <= |E|^2,

where sigma=2^(U.selection.level)*delta, Q is the actual retained distinct-output support, and kappa is the original recovered-two-ends choice(width,2B,theta^(-1),alpha,1).

The rho is the actual cumulative density of the constructed normalized colored incidence set. The proof invokes `ConstructedPivotClosing.construct` with U's actual selection and simultaneous slab data, and with the normalized all-radius spatial bound already derived inside U. That invocation constructs actual normalized tube/shading families, their finite colors, their retained incidence set, the actual upper degree-energy bound and the attached endpoint witnesses. No additional geometric, cap, retained-mass, incidence-count or energy assumption appears in this theorem.

## Exact fixed-factor separation

Put n=k+2 for original physical dimension. The actual lifted cap coefficient is

    [spatialConstant(n,width,baseRadius,d) * cutoff(U)]
      * [16+2*(2width+n/2)]^d.

`cap_factorization` proves its equality to geometricFactor*cutoff(U), where

    geometricFactor = spatialConstant(n,width,baseRadius,d)
                      * [16+2*(2width+n/2)]^d.

The factor is fixed before the scale, kappa, marked fraction, original cutoff and configuration. Its positivity follows from the separately proved spatial coefficient lower bound with L=1 and the positive graph-chart factor. The returned coefficient is exactly c0/geometricFactor, with c0 the uniform constructed-closing coefficient. No inverse kappa or scale loss is absorbed into a supposedly fixed constant.

The original versus normalized mesh and kappa conversion is already correctly included in c0 by ConstructedPivotClosing / SelectedOutputClosing. This module does not perform a second scale conversion. The original pruning cutoff is left literal and untouched for the numerical substitution.

The energy bound initially has |U.recovered.family.unionCells|^2 on the right. The proof explicitly invokes U.recovered.union_subset_E, casts actual cardinalities and applies monotonicity of the square to obtain |E|^2. It does not substitute original M, E or density silently.

## Scope and remaining composition

The lifted physical ambient dimension is k+3, while the package's original physical ambient dimension is k+2. Accordingly the selected-density coefficient uses local direction-dimension index k+1. This matches the previously audited dimension conventions.

The theorem needs only the lifted DiscreteEstimate and the already constructed original Package; its coefficient is also uniform over the original m,p,alpha carried by that package. Constructing U from a base DiscreteEstimate remains the preceding OriginalPivotSlabs theorem, with its original geometric and quantitative logarithmic-budget hypotheses. There are no further caller-supplied smallness tests because U already proves the attached-witness test.

Combining this theorem with U.sigma_lower, U.output_lower and the exact cutoff's base-estimate domination is the scalar fourth-power step currently assigned to the root. A completed final global estimate additionally needs the broader original reductions and coarse-scale treatment. This module proves the actual energy interface, not the final dimension conclusion by itself.
