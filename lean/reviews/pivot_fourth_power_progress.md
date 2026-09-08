# Spatial cutoff, marked angles, and the fourth-power pivot bound

New standalone module: `PivotFourthPower.lean`. It inspects and composes the exact current numerical interfaces after `ClosingEnergyAlgebra`, and proves the fourth-power and exact fourth-root formulas. Shared modules are unchanged.

## Original comparison values and density

`recovered_angle_count` applies the actual marked-angle theorem to `MarkedPruningAssembly.RecoveredInput`. It proves

|angles| ≥ ξ² λ² M²/[128 δ² E],

where M and E are the original comparison tube count and occupied-set cardinality. Neither is replaced by the potentially smaller recovered population. The marked mass is ξλM/(8δ), so its square and the marked-angle factor 1/(2E) give exactly 1/128. The only angular input is the actual 2κ≤θ condition.

`recovered_density_power` proves λ_recovered^v ≥ 2^(-v)λ^v for v≥0, from the record's literal choice λ_recovered=λ/2 or λ. For (5.34), use v=2q+2+2ε; this contributes only a fixed coefficient. The angle bound still uses original λ.

## The literal max cutoff

The existing assembly uses the actual cutoff

F_raw = max{1, K E A₀ δ^(d−m−ε) η^(-(p+1)) λ^(-p)/M},
η = ξ/[100(J+1)].

It does not simply state the paper's displayed (5.6). The new inverse-base and max-cutoff lemmas handle this distinction. If the original base estimate gives

E ≥ c_base A₀⁻¹ δ^(m−d+ε) λ^p M,

then its inverse normalized expression is at least c_base. Since 0<η≤1 and p≥1, the maximum is bounded with the fixed coefficient K+1/c_base. No adjustment of the already chosen pruning constant K is needed.

Using J+1≤L, 0<δ≤1, 0<ξ≤1 and ε≥0, `actual_cutoff_upper` proves

F_raw ≤ C_F E A₀ δ^(d−m−2ε) ξ^(-(p+1)) L^(p+1) λ^(-p)/M,
C_F=(K+1/c_base)·100^(p+1).

The actual cutoff starts with one ε scale loss; weakening it to two gives precisely the source convention. The original cap coefficient A₀ remains explicit. If the lifted family uses F=C_lift F_raw, multiply C_F by that fixed normalization coefficient. Its independence of κ and δ must come from the actual geometric cap construction.

## The E⁴ substitution

`fourth_power_substitution` proves the general real-exponent cancellation, using exactly the cutoff upper bound, angle lower bound, and the preceding E² estimate. `source_fourth_power` specializes it to (5.34), including the verified κ weakening for ε≤1:

E⁴ ≥ (c c_angle/C_F) κ^(5n+6q+12) A₀⁻¹
      ξ^(p+3) L^(-(p+4)) δ^(m−d′−3+3ε)
      λ^(p+2q+4+2ε) M³.

Here n is projective direction dimension, one below the original ambient dimension. It is the same convention as the scalar density lemmas in ClosingEnergyAlgebra. All other displayed exponents and cap parameters are real.

`source_fourth_power_density` uses the literal identity S=Mδ^m and proves

E⁴ ≥ (c c_angle/C_F) κ^(5n+6q+12) A₀⁻¹
      ξ^(p+3) L^(-(p+4)) δ^(-2m−3−d′+3ε)
      λ^(p+2q+4+2ε) S³.

Thus the N=δ⁻¹ exponent is exactly 2m+3+d′−3ε, agreeing with (5.3). Both inverse factors of original E have been multiplied to the left; no retained-population substitution is used.

## Exact fourth root and population linearization

`fourth_root_bound` roots the full positive monomial and exposes the existing scalar maps

D=(2m+3+d′)/4,  C=(p+2q+4)/4.

Before absorbing conditioning logarithms, it gives the exact scale and density factors δ^(-D+3ε/4) and λ^(C+ε/2), with κ, ξ and logarithm factors all raised to their quarter powers and S^(3/4). It requires only E≥0 and positive monomial bases; it does not assume an integer exponent or silently take a signed fourth root.

`population_linearization` proves C₀^(-1/4)S≤S^(3/4) whenever 0<S≤C₀. The source's fixed cap normalization can therefore turn S^(3/4) into S with an explicit fixed coefficient.

## Exact remaining interfaces

The numerical theorems consume (5.34) in the precise form already produced by ClosingEnergyAlgebra.source_from_energy; they do not assume the desired E⁴ or fourth-root conclusion. Actual marked angles are obtained directly from the recovered record. The original base estimate and actual pruning cutoff match the proved max-normalization lemmas.

Root is separately handling the normalization bridge: actual grouped closing uses δn=δ/(1+2width), κn=κ/(1+2width), whereas output count and σ use original δ,κ. The corresponding fixed factor (1+2width)^(-(5+d−d′+1+ε)), or its κ⁶ analogue, and the normalized ρ constant must be included in the fixed closing coefficient before invoking these original-scale substitutions.

The remaining full pivot work is identifying every actual selected lift, normalized group, pruning incidence, attached sample and density in one concrete construction. Polynomial-log conditioning absorption and the later angular/two-ends globalization are not asserted by this module. The exact fourth-root maps and all visible powers are proved; the unconditional final pivot/endpoint theorem is not claimed.

## Verification

Lean4.33.1 and mathlib commit 0df444a360eaa60ab8c11dca51a86af692955474. Final source, olean and full-source axiom-audit status will be recorded below.


Final verification: all 13 theorems compile without errors or warnings, the current olean is built, and the full-source audit prefix matches the final source. Every theorem depends only on propext, Classical.choice, and Quot.sound; no sorry or custom axioms occur. SHA-256: `3d1df603c1e61fc155c53cc1f067af1d02511763b294c96679da10a9d8f26921`.

Commands from `audit_work/formalization`:

```
/Users/ssoh/.elan/bin/lake env lean -o .lake/build/lib/lean/PivotFourthPower.olean PivotFourthPower.lean
/Users/ssoh/.elan/bin/lake env lean ../pivot_fourth_power_axioms.lean > ../pivot_fourth_power_axioms.log
```
