# Square-root cap loss: finite all-angle two-ends seed

`AngularSeedSqrtCap.lean` is frozen and clean compiled. SHA-256: `f5bcb023e39a0d9639cddf4e6b722036dafa20a3ad8670aa990b11d92109dd77`.

The exact-source environment audit passes all eight local theorem declarations (six source theorems), using only `propext`, `Classical.choice`, and `Quot.sound`. There are no custom axioms, `sorry`, or diagnostic warnings. The audit data are `AngularSeedSqrtCap_audit.json` and `AngularSeedSqrtCap_axioms.log`.

The new theorem preserves the exact cap dependence that the earlier general seed weakened: the logarithmic hairbrush constant is its value at cap coefficient one divided by `sqrt A`. This identity is carried through actual angular selection, retained-family counts, and union summation. Both an explicit logarithmic form and a version absorbing logarithms into any positive scale error are proved. Constants precede every scale, density, family, and cap coefficient.

For actual finite grid shadings in ambient dimension `n=k+2`, `m>1`, comparable full density `lambda/delta <= #shade_i <= 2 lambda/delta`, and actual per-tube two-ends bound with coefficient at most `B0*log(2/delta)^b`, the natural-logarithm theorem gives

`c * A^(-1/2) * log(2/delta)^(-P) * lambda^2 * M * delta^((m-3)/2) <= #unionCells`,

with `c>0`, `P>=0` depending only on fixed dimension, width, two-ends exponent/budget, and `m`. It needs no bounded tube-position hypothesis. The actual finite family is direction-separated and satisfies the stated real-exponent cap bound. Its complete source statement is the specification; the displayed formula abbreviates its actual geometry hypotheses.

This is not yet the standalone arbitrary-measurable statement (4.1)/(4.4). The old discrete-to-measurable theorem requires a different exponent regime and would not preserve this exact square-root/logarithmic result. The remaining bridge is weighted angular selection on exact measurable incidence-pattern atoms, followed by actual measurable group compression and the existing measurable single-angular-group hairbrush theorem. Whole-cell replacement is deliberately not used to infer original measurable-union volume. Fixed logarithmic lower/upper density ratios likewise remain to be assembled for the continuous theorem.
