# Actual finite dyadic approximation

`DyadicApproximation.lean` constructs actual finite inputs for the proved RestrictedInterpolation interface. The index set is the integer interval [-N,N]. At each j<N, the actual band is {2^j≤f<2^(j+1)}; the terminal j=N band is {2^N≤f}. Heights are exactly the frozen NNReal `dyadicHeight j`, and the actual approximation is literally `bandSum (indices N) dyadicHeight (bands f N)`.

All bands are measurable for measurable f and pairwise disjoint on the actual finite index set. At any point in a band, the entire sum is exactly that band's height. The approximations stay below f and increase with N. The increasing claim includes the changes to terminal bands: a largest qualifying index in the larger finite index set constructs the actual new band. No projection-injectivity, nonzero input, or assumed logarithmic index witness is used.

The actual supremum of these sums satisfies `f≤2*sup_N approx` pointwise for every ENNReal-valued function. Finite positive values are placed between adjacent integer powers by Mathlib's Archimedean theorem. For an infinite value, the terminal band gives the value 2^N at every N and unboundedness of powers proves the supremum is infinite. Zero values are handled directly. Therefore the terminal-band construction avoids any AE-finiteness or finite input-integral hypothesis.

The module uses only frozen RestrictedInterpolation and standard Mathlib facts; it does not rely on an interpolation theorem. It supplies the actual finite disjoint measurable inputs and monotone pointwise approximation for the remaining strong-type extension.

Clean build, zero diagnostics, frozen SHA256 dcaa6372f871f3ff136e9f86b11aaf52fcdc0dc16636feba66e7d5cd04c90d61. Exact-source audit PASS19 named declarations (3 definitions,16 theorems), standard foundations only. No custom axiom or sorry; source-prefix/hash and complete expected-declaration checks passed. Audit files/log/meta are DyadicApproximation_full_source_audit.* in audit_work.
