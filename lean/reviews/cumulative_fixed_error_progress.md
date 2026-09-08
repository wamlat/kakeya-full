# Literal fixed-error cumulative estimate

`CumulativeFixedError.lean` is frozen at SHA-256 `266e9eb0435e9e665335b633e07301ffc23dcc5d06ac911f0c9d29742a7ba961`. It is a new development source outside the 406-source checkpoint-22 freeze; no existing source or registry was edited.

The module closes combined Corollary 1.1, display (1.6), as a public theorem. `from_fixed_input` chooses a positive multiplier `cr` using only dimension, fixed geometry, and density exponent `p>=1`. After that choice it quantifies over the cap parameter, set exponent, one fixed error, input coefficient `c>0`, cap coefficient `A`, and upper scale cutoff. Its analytic premise applies only to comparable configurations at that exact `A` and cutoff. It concludes

`cr*c*A^(-1)*delta^(m-d+error)*s^p*M / log(2/delta) <= #actualUnion`.

`source_notation` exposes the identical formula `cr*c*A^(-1)*N^(b-m-error)*s^p*M/log(2*N)` with `N=1/delta`. There is no every-positive-error hypothesis, no extra scale loss, no uniform-in-A input premise, and no large-scale extension needed when the cutoff is `1/2`.

The proof constructs actual equal-cardinality subfamilies from the original rows and explicitly preserves both scale and cap coefficient. The actual finite dyadic classes include the zero class, cost only `J+2`, and obey an exported uniform linear logarithm bound. It reuses the verified cardinality bins and finite convexity argument. All subfamily unions are contained in the original union. The final constant is `1/((4*C)^p*B)`, where `C` is the actual fixed tube-cell count constant and `B` the linear-log constant. It is independent of cumulative density, scale, population, positions, cap coefficient, and the fixed analytic error.

Empty total population is handled directly. Empty individual rows, arbitrarily unequal rows, `s=0`, `0<s<delta`, and densities above one at a fixed geometric bound remain permitted. Normalization of individual bin densities uses actual trimming and does not impose `s<=1` on the final input. Positivity of the denominator is proved even at `delta=1`.

Validation used Lean 4.33.1 and pinned mathlib `0df444a360eaa60ab8c11dca51a86af692955474`:

```
lake env lean -o .lake/build/lib/lean/CumulativeFixedError.olean CumulativeFixedError.lean
python3 ../audit_cumulative_fixed_error.py
```

Compilation returned zero diagnostics. The exact-source production audit passed all five named source theorems, twelve local theorem declarations, and twelve total local declarations, with only `propext`, `Classical.choice`, and `Quot.sound`. There are no custom axioms, `sorry`, `admit`, or `native_decide` occurrences. Evidence is in `cumulative_fixed_error_audit.json` and `CumulativeFixedError_SourceAudit.log`. Independent finite-agent review is saved in `cumulative_fixed_error_finite_review.md` at the same hash.

This is a proved conditional conversion on the project's actual normalized geometric configuration class. It supplies the missing single-error cumulative conclusion; it does not postulate or independently prove a new analytic Kakeya input. The earlier every-error cumulative theorem and all frozen applications remain unchanged.
