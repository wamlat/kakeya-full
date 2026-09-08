# Full fractional cap range and literal cumulative exponents

`FractionalSeedFullRange.lean` compiles without diagnostics and passes an
exact-source audit of all six local theorem declarations. Its frozen source
hash is `319aa2a0e18b601051cc29520d2a5702fac9fa7edbaa371e24b45aaf6d9f9642`.
All dependencies are standard foundations, with no custom axiom.

The existing constructive unrestricted fractional seed had a public m>3
hypothesis, while its lower components already allowed m>1. This module
assembles that proof over the full m>1 range. The only relevant sign choices
are d=(m+3)/2>2, eta>0, alpha=eta/(d+eta) in (0,1), and
beta=(m-1)/4>0 with beta<=(m-1)/2. The actual covered seed needs m>=1;
cap-preserving normalization needs m>=0. No argument needs m>3.

`fractional_discrete_seed` proves the actual arbitrary-shading estimate in
ambient k+2, uniformly before the configuration. It constructs the common
normalized cover, localization, direction thinning and measurable hairbrush
application through the same previously proved components. Integer shading
density and the actual logarithm absorb all losses. The empty family is
included. `fractional_real_cap_seed` provides every legal ambient instance.

`fractional_cumulative_seed` and `fractional_real_cap_cumulative` include
unequal and empty shadings, with no lower cutoff on cumulative density.
`source_cumulative` proves the precise source powers in (4.29)/Corollary4.3:

`c A^(-1) delta^((m-3)/2+epsilon) sigma^((m+3)/2+epsilon) M <= union cardinality`.

The constant is chosen after the fixed geometry, m and epsilon, before every
actual cumulative configuration. Density weakening precedes the cumulative
conversion, so no unjustified monotonicity at cumulative density greater than
one is used.

This closes the standalone lower-cap-range wrapper for Lemma4.1 and
Corollary4.3, including 1<m<=3. The separate continuous all-angle A^(-1/2)
statement and sharpness pencil remain distinct obligations. This addition is
outside frozen checkpoint18 and belongs to a later verification checkpoint.
