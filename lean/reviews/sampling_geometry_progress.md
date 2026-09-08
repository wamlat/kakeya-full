# Variable-length geometry and exact raw probability transport

`SamplingGeometry.lean` is frozen and cleanly compiled, with complete-source axiom audit PASS: seven named theorems, fourteen local theorem declarations, fifteen all local declarations; standard foundations only. SHA256:726dde39fb3915ff83e1b9991e2e4d5ffd33747d72d019285190e4609ef06e0a.

`lengthCarrier T length width` is the literal set of points within the indicated width of an axis parameter t in[0,length], where T retains the original base and unit direction. A common positive dilation W normalizes every original length≤W into an actual unit carrier, preserving direction. Fixed c*delta separation implies new-mesh delta/W separation once1≤cW.

The map has exact half-open grid membership and image identities, including boundaries. Hence the raw cell-intersection weights are identical after the simultaneous change x↦x/W and delta↦delta/W, with the original integer cell labels unchanged. The full and marked positive support labels are also identical. No row-dependent normalization or rounding is introduced.

These are geometric transport primitives. The subsequent comparable-length sampling assembly will use direct bounded-support identities at the original delta, preserving the original physical ball and angular test radii. Thus this module alone does not assert a new complete sampling theorem or silently change its angular conditioning.

Clean compilation: `lake env lean -o .lake/build/lib/lean/SamplingGeometry.olean SamplingGeometry.lean`. Complete-source audit: `lake env lean ../sampling_geometry_axioms.lean` with production AUDIT. Adjacent JSON and log preserve exact details.
