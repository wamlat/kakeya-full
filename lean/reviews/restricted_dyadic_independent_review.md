# Independent finite dyadic distribution review

Reviewed the exact frozen `RestrictedDyadic.lean`, hash
`2ccda36c4ef1c6bb1bc0d4f1a7b53eac24a8e3dac61a5d766d3a32bebe02dfe4`.
No mathematical defect was found.

The cutoff J is constructed from the floor of log(t)/log(2), so the actual
positive threshold lies between the adjacent dyadic heights. The geometric
weight uses the injective nonnegative offset j-J-1 for the actual high bands.
Its lower bound by `(1-q)(t/height_j)^gamma` uses t<=height_(J+1), followed by
nonnegative real-power monotonicity. Raising the weighted threshold to -a
reverses the relevant inequality because a>0. This gives the advertised
exponent b=a(1+gamma) with q=2^(-gamma), 0<q<1.

The final distribution theorem applies the previously proved indicator-only
finite-superposition bound, then replaces the high-band index set by
`{j in s | t<height_j}`. The proved subset direction enlarges a sum of
nonnegative ENNReal terms, as required. The constants have no dependence on
the number of bands. Infinite band measure or infinite operator values are
allowed; the estimate uses measure monotonicity and finite unions without
assuming output measurability.

This is an actual finite-input distribution estimate. It is not a strong Lr
estimate until layer cake and power integration have been supplied, and it is
not a result for arbitrary input functions until the approximation argument
has been supplied. The source preserves both boundaries explicitly.
