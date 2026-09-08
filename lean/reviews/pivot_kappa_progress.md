# One explicit legal and transverse pivot parameter

`PivotKappa.lean` is complete: 13 theorems and 2 definitions, cleanly compiled and built. It defines a single actual choice

`κ = (16B)^(-1/α) (2K)^(-1/β) / [100(2·width+1)]`.

Equivalently this uses the existing proved concentration radii `concentrationRadius(8B,α)` and `concentrationRadius(K,β)`. The product form avoids separate existential choices or an opaque minimum.

For nonnegative width, `B,K≥1` and positive α,β, the bundled theorem `admissible` proves simultaneously:

- `0<κ≤1/100`;
- `(2·width+1)κ≤1`;
- `B((2·width+1)κ)^α≤1/16`, the legal-sample physical exclusion;
- `K(2κ)^β≤1/2`, the marked-direction half-cap test.

From positive B₀,K₀,L and budgets `B≤B₀L^b`, `K≤K₀L^q`, `choice_log_lower` proves

`choice(width,B₀,K₀,α,β) L^(-(b/α+q/β)) ≤ κ`.

The prefactor is positive, fixed before the density and scales, and the exponent has no density dependence. `loss_nonneg` verifies its nonnegativity when b,q are nonnegative. `normalized_choice_log_lower` keeps this same exponent under the common homothety `κ↦κ/R`. `normalized_legal_two_ends` additionally verifies the exact cancellation with the normalized physical coefficient `B R^α`, preserving the `1/16` test.

The scale condition remains explicit. `scale_admissible` proves `δ≤κ` from the transparent scalar test that δ is at most the displayed logarithmic lower bound. This module does not assume or silently derive a sufficient `Nκ^20` cutoff. That larger-scale threshold remains a separate scalar/application obligation.

`PivotKappaAudit.lean` audits every new theorem. The main geometric-test and logarithmic-bound axioms are only standard `propext`, `Classical.choice`, and `Quot.sound`; there are no custom axioms or unproved placeholders. The module leaves all previously frozen files unchanged.
