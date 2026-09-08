# Unrestricted real-cap pivot and recursive endpoint

`UnrestrictedPivot.lean` is frozen, clean-built, and audited against its complete exact source. Three source theorems and five local theorem declarations depend only on standard Lean foundations. SHA-256: `724ccc29a18566f85f3f928b742e10a901b0b4596646b3106bb9b381bdbb0722`.

`real_cap_pivot` proves the full recursive interface formerly assumed by `SeededEndpoint`. From actual `RealCapEstimate m d p` and `RealCapEstimate d d' q`, with `3<d'<d<m`, `d≤p`, and `d'≤q`, it proves the actual unrestricted estimate at set exponent `(2m+3+d')/4` and density exponent `max((2m+3+d')/4,(p+2q+4)/4)`.

Every ambient dimension adequate for m is covered. The base is applied in that actual ambient n and the lifted estimate in ambient n+1. The ordering assumptions derive every all-angle branch restriction, including the strictly positive sparse margin `(p+2q+5−3d')/12`. Actual `TwoEndsGlobalization.remove_two_ends` then removes the full two-ends hypothesis. No marking, angular decomposition, sampling outcome, localization, spatial partition, conditioning budget or population bound is supplied by the caller.

`real_cap_endpoint` supplies this proved pivot and the proved fractional seed to the constructive real-cap iteration. The result has set exponent `3+(2−sqrt(2))*(m−3)` and density exponent the maximum of this value and four. `diagonal_endpoint` gives the actual diagonal discrete estimate at `3+(2−sqrt(2))*(n−4)` for every integer n≥6. Neither endpoint has a seed or pivot premise, and neither uses the published custom axioms.

These are actual finite-grid configuration statements with each fixed normalization preceding its uniform estimate constant. They do not themselves remove the bounded-position normalization or assert an operator norm theorem. Measurable, cap-free, arbitrary-position and maximal-operator interfaces remain separate named deductions.

Evidence: `unrestricted_pivot_axioms.lean`, `unrestricted_pivot_axioms.log`, `unrestricted_pivot_audit.json`, and the independent `unrestricted_pivot_independent_review.md` (no defect found).
