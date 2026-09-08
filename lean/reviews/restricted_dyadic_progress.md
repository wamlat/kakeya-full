# Constructed dyadic distribution estimate

`RestrictedDyadic.lean` is frozen and clean-built. Its exact-source all-declaration audit passes: 8 named theorems, 21 local declarations (20 theorem declarations), standard foundations only. SHA256 `2ccda36c4ef1c6bb1bc0d4f1a7b53eac24a8e3dac61a5d766d3a32bebe02dfe4`.

For every positive threshold t the module constructs J=floor(log t/log2) with 2^J≤t<2^(J+1). It sets q=2^(-γ), proves 0<q<1 for γ>0, and proves that the actual normalized geometric weights dominate (1-q)(t/2^j)^γ on all bands j>J. This is then composed with the frozen actual low/high decomposition and the indicator-only weak estimate.

The final `dyadic_distribution` statement is a uniform outer-measure estimate for every finite pairwise disjoint measurable family E_j and actual function f=Σ 2^j 1_Ej:

ν{Tf>2t} ≤ Σ_{j:t<2^j} ofReal[A(1-q)^(-a)(t/2^j)^(-a(1+γ))] μ(E_j).

All constants are independent of the number of bands, their locations, t, and E_j. The assumptions are elementary positive operator laws and the original weak estimate for the individual indicators; no general-input weak estimate or interpolation conclusion is assumed. Infinite E_j and infinite outputs are allowed, since the result is an ENNReal outer-measure inequality.

The strict exponent margin for integration will be a(1+γ)<r, with γ chosen from fixed a<r. Integrating this actual distribution, converting the dyadic input sum to its Lr integral, and monotone extension are subsequent modules under active construction. This module itself does not claim a completed strong Lr norm theorem.

Audit files: restricted_dyadic_axioms.lean/log and restricted_dyadic_audit.json. Reproduce with `lake env lean RestrictedDyadic.lean` and `lake env lean ../restricted_dyadic_axioms.lean` from the development package.
