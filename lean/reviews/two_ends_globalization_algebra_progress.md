# Section 8 two-ends globalization: scalar composition

`TwoEndsGlobalizationAlgebra.lean` is clean-built and stable. It proves nine named theorems and defines two explicit quantities. The complete source plus the production all-local-declaration audit compiled without any diagnostic output other than its audit entries. All 13 local environment declarations, including 11 theorem entries, depend only on `propext`, `Classical.choice`, and `Quot.sound`.

Source SHA-256: `dafd5a706b1351bb1c51ca252c6a2f42ab5d4f8f7eeb7ec046ecfdcae945d356`.

The source comparison is with Proposition 8.1 and equation (8.1) of the combined PDF, as extracted in `audit_work/source/combined.txt`, lines 1654–1701. `LogLoss.lean`, `PivotLossAbsorption.inverse_log_delta`, and the earlier specialized `SeedGlobalizationAlgebra.lean` were inspected before implementing the general density-exponent transition.

## Exact power identities

For positive mesh, radius, and localized density, `localized_scaling_identity` proves

`(δ/ρ)^(m−D+η) (ν/ρ)^C ρ^m = δ^(m−D+η) ν^C ρ^(D−C−η)`.

All exponents are real. The thinning fraction contributes exactly `ρ^m`; there is no ambient-dimension power in this identity. `localized_scale_loss` then proves, for `ρ ≤ 1` and `η ≥ 0`,

`δ^(m−D+η) ν^C ρ^(D−C) ≤ (δ/ρ)^(m−D+η) (ν/ρ)^C ρ^m`.

This checks explicitly the inequality direction when the nonnegative loss in the radius exponent is discarded.

## Density-exponent transition

Define `P = max D C` and `g = G^(-max(D−C,0))`. For `0 < ρ ≤ 1`, `ν > 0`, `G ≥ 1`, and `ν ≤ Gρ`, `density_collapse` proves

`g ν^P ≤ ν^C ρ^(D−C)`.

When `C ≤ D`, this raises `ν/G ≤ ρ` to the nonnegative exponent `D−C`. When `C > D`, it uses `ρ^(D−C) ≥ 1`. The coefficient `g` is explicit and strictly positive.

`density_lower` also proves the exact substitution

`cNu^P L^(-aP) δ^(αP) λ^P ≤ ν^P`

from `ν ≥ cNu L^(-a) ρ^α λ`, `δ ≤ ρ`, `α ≥ 0`, and `P ≥ 0`. Positivity conditions are explicit. The full logarithmic exponent is `aP`.

## Uniform absorption and quantifiers

`uniform_factor_absorption` fixes `D,C,G,cNu,a,α,η,eps`, requiring `P ≥ 0`, `G ≥ 1`, `cNu > 0`, `a,α ≥ 0`, and

`η + αP < eps`.

It chooses a positive constant before every `m,δ,ρ,ν,λ`, and derives

`c δ^(m−D+eps) λ^P ≤ δ^(m−D+η) ν^C ρ^(D−C)`

for `0 < δ ≤ ρ ≤ 1`, positive densities, `ν ≤ Gρ`, and the stated logarithmic lower bound at `L = log(2/δ)`. The absorption uses the strictly positive fixed margin `eps−η−αP` and the existing uniform inverse-log theorem. The conclusion holds for every mesh in this range, rather than only after a configuration-dependent threshold.

`uniform_localized_bound` composes this factor estimate with a genuine localized lower bound, preserving any nonnegative weight `S`. Thus a cap factor and a population can be carried together without an additional exponent loss.

The top theorem `uniform_globalization`, in the requested range `D,C ≥ 1`, has this quantifier order:

1. Fix `D`, `C`, and `eps > 0`.
2. Choose `0 < α < 1` and `η > 0`.
3. Allow the fixed geometric bound `G ≥ 1`, fixed density coefficient `cNu > 0`, fixed localized-estimate coefficient `cLocal > 0`, and fixed logarithmic exponent `a ≥ 0` to depend on those chosen losses.
4. Choose `c > 0` before all meshes, localization radii, densities, cap coefficients, populations, and union counts.
5. From the actual scalar premises and

   `cLocal A⁻¹ δ^(m−D+η) ν^C ρ^(D−C) M ≤ E`,

   conclude

   `c A⁻¹ δ^(m−D+eps) λ^P M ≤ E`.

The explicit loss allocation is `α = min(1/2, eps/(4P))`, `η = eps/4`, leaving at least `eps/2` for logarithmic absorption. This order permits the constants and logarithmic exponent supplied by the two-ends theorem to depend on `α`, as the source requires. The scalar theorem allows every `A > 0` and `M ≥ 0`, so the usual `A ≥ 1` and natural-cardinality cases are included.

The set exponent remains **D**. Replacing `m−D` by `m−P` would strengthen the set estimate when `C > D` and is not justified by this argument. Raising the density exponent alone is exactly the conclusion of source Proposition 8.1.

## Remaining geometric boundary

This is a conditional scalar composition. It does not construct shortest-scale localization, derive the lower and upper localized-density inequalities, select the common parameter class, assign disjoint spatial groups, perform the coarse cap thinning, invoke the all-angle two-ends estimate on an actual normalized family, or sum those groups to establish equation (8.1). The local power identity checks the arithmetic of those operations without assuming their geometry has been constructed.

The wrapper's premise is the explicit localized lower bound from (8.1), not an unrestricted final conclusion. The existing specialized seed-globalization module remains unchanged; this module supplies the general `max(D,C)` density transition required for the recursive pivot. It does not claim a complete formal proof of Proposition 8.1's geometric reduction or the unrestricted Kakeya theorem.

No existing/frozen module, common Lake file, verifier, external-axiom registry, or published snapshot was edited.

## Verification artifacts

Commands in the matching development Lean project:

```sh
lake env lean -o .lake/build/lib/lean/TwoEndsGlobalizationAlgebra.olean TwoEndsGlobalizationAlgebra.lean
lake env lean ../two_ends_globalization_algebra_axioms.lean
```

The generated audit source, actual Lean output, and machine-checked inventory/hash result are `audit_work/two_ends_globalization_algebra_axioms.lean`, `audit_work/two_ends_globalization_algebra_axioms.log`, and `audit_work/two_ends_globalization_algebra_audit.json`. The check verifies the exact source prefix, every named theorem's audited presence, all-local-declaration axiom closure, no forbidden source constructs or compiler diagnostics, and a fresh compiled `.olean`.
