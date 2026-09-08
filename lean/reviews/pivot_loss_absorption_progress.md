# Uniform conditioning, density-error, and population loss absorption

New module: `PivotLossAbsorption.lean`. This closes the numerical loss absorption after the genuine fourth-power pivot estimate. It does not assume a first-power Kakeya bound, a desired error-free estimate, or the desired endpoint theorem.

## Constants and quantifier order

`pivot_small_scale_absorption` chooses e=min(1/2,epsilon/4), so 0<e≤1. Only after choosing e does it accept the positive raw fourth-power constant c₀, which may depend on e. It then chooses a positive threshold δ₀≤1 and a positive output constant c, before δ,κ,ξ,λ,A,S,E or any configuration is supplied. All other input parameters are fixed conditioning budgets, dimensions/exponents, and normalization constants.

The input fourth-power estimate is the already checked original-scale expression

E⁴ ≥ c₀ A⁻¹ κ^H ξ^P L^(-Z) δ^(-4D+3e) λ^(4C+2e) S³,

where L=log(2/δ), H=5n+6q+12, P=p+3, Z=p+4, n is the projective direction dimension, D=(2m+3+d′)/4, and C=(p+2q+4)/4. Neither D nor C depends on the two-ends exponent.

## Explicit conditioning budgets

The only conditioning inputs are

κ ≥ κ₀ L^(-a),  ξ ≥ ξ₀ L^(-b),

with fixed κ₀,ξ₀>0 and fixed a,b≥0. The exact combined logarithmic loss is

T_log = aH+bP+Z.

`conditioning_lower` derives the resulting product bound from these actual lower budgets. `inverse_log_delta` derives a uniform positive logarithmic absorption coefficient from the existing LogLoss theorem, in the physical δ variable. No hidden δ-dependent constant is introduced.

The actual base-two depth logarithm is also handled: `pivotLog_natural_upper` proves

pivotLog(δ) ≤ [3/log(2)] log(2/δ),

and `pivotLog_inverse_power` gives the corresponding lower bound for every inverse nonnegative power. Thus the preceding actual fourth-power theorem can use the natural-log interface here with a fixed coefficient change.

## Genuine removal of the density error

For nonempty integer-grid configurations, the already proved bound λ≥δ/2 is available. `density_log_fourth` applies ErrorAbsorption.density_log_product at eta=2e. Absorbing a log power with δ^(2e), and paying for λ^(2e), introduces exactly δ^(4e). Together with the original δ^(3e) error, the fourth-power error is exactly 7e.

Since 7e≤4epsilon, monotonicity for δ≤1 weakens this to the target δ^(-4D+4epsilon). The fourth root therefore has the exact density power λ^C, without a residual density error. This is stronger than the source's displayed λ^(C+epsilon) for 0<λ≤1. The finite lower-density premise is explicit in the scalar theorem; it is not asserted for arbitrary measurable shadings.

## Population and inverse cap dependence

The scalar theorem permits the varying population budget S≤C_pop A, not merely a fixed S bound. `cap_population_linearization` proves

C_pop^(-1/4) A⁻¹ S ≤ A^(-1/4) S^(3/4),  when A≥1.

Thus the fourth root of the input inverse-cap coefficient and the population factor together give the required linear A⁻¹ coefficient, with a fixed C_pop^(-1/4) loss. No uniformity in A is lost.

`configuration_population_bound` derives S=Mδ^m≤packingConstant(n) A from the actual TubeFamily.CapBound total-count theorem. `configuration_absorption` specializes the numerical result to actual ShadedConfigurations, derives both λ≥δ/2 and the population bound internally, and concludes

c A⁻¹ δ^(m−D+epsilon) λ^C M ≤ |unionCells|.

Its remaining premises are precisely the explicit κ,ξ conditioning budgets and the concrete original-scale E⁴ inequality for that configuration. It does not assume this desired first-power conclusion.

## Uniform geometric small-scale threshold

`polylog_small_scales` turns κ≥κ₀L^(-a) into a positive δ₀ chosen before κ or δ, such that every 0<δ≤δ₀ satisfies

δ≤κ,  T≤δ⁻¹κ²⁰,

for any prescribed fixed real T. It derives a δ^(1/40) lower bound for κ from the log theorem and invokes the existing PivotKappaScale.power_lower_cutoff. The main small-scale theorem returns these conditions alongside the estimate. Actual κ≤1 and a sufficiently large fixed T can then imply the several lower-power geometric smallness conditions; those concrete fixed-normalization choices remain part of the geometric assembly.

## Remaining geometric inputs, exactly

1. The earlier selected output, common normalized lift, grouped pruning, and attached-sample constructions must supply the E⁴ estimate on the same original configuration. The fixed normalized-to-original factors supplied by SelectedOutputClosing and SelectedOutputDensity must already be included in c₀.
2. A κ lower budget follows from the existing explicit PivotKappa choice once upper polylogarithmic budgets for the original two-ends coefficient and inverse marked angular radius have been established. Its fixed width/normalization factor belongs in κ₀. This module does not invent those concentration budgets.
3. The original marked fraction must have the stated ξ≥ξ₀L^(-b) lower budget. Establishing it for the angular-conditioning construction is still a geometric/combinatorial step.
4. The population and finite lower-density budgets are no longer external gaps: they are derived in the configuration-facing theorem.
5. CoarseBounds.DiscreteEstimate.of_small_scales already extends an actual uniform small-scale estimate to all scales. Applying it here requires the raw fourth-power/conditioning construction for every relevant full configuration (and trivial handling of M=0). That universal geometric premise, including the later angular and two-ends reductions, is not asserted by this numerical module.

The conditioning exponents and threshold may depend on the fixed two-ends exponent and normalization. The dimension and density maps remain exactly D and C. No unconditional final pivot or endpoint estimate is claimed.

## Verification

Lean4.33.1 and mathlib commit 0df444a360eaa60ab8c11dca51a86af692955474. Final clean compile, current source/olean, and full-source axiom audit will be recorded below.


Final verification: all 13 theorems clean-compile, the current olean is built, and the full-source audit prefix matches the final source. All 13 axiom audits use only propext, Classical.choice, and Quot.sound. No errors, warnings, proof placeholders, custom axioms, or residual tactic diagnostics occur. SHA-256: `03e3a28e1e1caf506f0340fb7122fbceece8fe86892d6d9db373dd40a68bc011`.

Commands from `audit_work/formalization`:

```
/Users/ssoh/.elan/bin/lake env lean -o .lake/build/lib/lean/PivotLossAbsorption.olean PivotLossAbsorption.lean
/Users/ssoh/.elan/bin/lake env lean ../pivot_loss_absorption_axioms.lean > ../pivot_loss_absorption_axioms.log
```
