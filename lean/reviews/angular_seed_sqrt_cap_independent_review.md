# Independent review of the finite square-root cap seed

Reviewed the exact source `AngularSeedSqrtCap.lean`, its `finite_seed_at_depth` input, and the exact cap-prefactor identity in `AngularSeedLogLoss`. No substantive defect found.

- The square-root factor follows from an exact identity for the existing analytic prefactor. The new proof does not replace a previously weakened A^(-1) inequality with a stronger conclusion; it returns to the unweakened finite-depth bound and the exact linear dependence of `capCoefficient` on A.
- The positive constant and logarithmic exponent are chosen from the fixed dimension, width, alpha, B0, b, and m. Neither depends on the actual A, delta, lambda, tube count, angular depth, or selected pieces.
- The volume-to-cardinality cancellation is exact: delta^(k+1) delta^((m-1)/2) / delta^(k+2) = delta^((m-3)/2).
- For m>1, beta=min(1/2,(m-1)/4) is positive and satisfies beta≤(m-1)/2. All pieces are subsequently constructed from the actual family; zero population is handled explicitly.
- The natural-log conversion has the correct inequality direction for the negative loss exponent. The old seed logarithm is bounded above by a fixed multiple of log(2/delta), and the resulting fixed factor is included in the final positive constant. The B budget transfers in the opposite direction using the proved lower comparison.

The theorem concerns actual finite grid shadings satisfying full two ends. It does not by itself assert an arbitrary-measurable angular decomposition or a continuous union-volume theorem. Its docstring and public statement preserve that boundary.

Reviewed SHA256: `f5bcb023e39a0d9639cddf4e6b722036dafa20a3ad8670aa990b11d92109dd77`.
Independent recompilation command: `/Users/ssoh/.elan/bin/lake env lean AngularSeedSqrtCap.lean` in the development formalization project. Independent recompilation completed with exit code 0 and no diagnostics.
