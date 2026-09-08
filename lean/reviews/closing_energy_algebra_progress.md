# Closing pivot energy and source (5.34)

New module: `ClosingEnergyAlgebra.lean`. This phase derives (5.33) from the exact pruning threshold and exact actual attached-sample witness, then combines it with the already verified (5.19) population and σ lower bound. It does not assume (5.33) as an input to the final `source_from_energy` theorem.

## Exact current conventions

`GroupedCumulative.discrete_pruning` defines Q=Σ_g M_g, ρ=δ|S|/Q, a=c A⁻¹ δ^(d−d′+ε), and

H = 2^(r+1) J (1/δ)/(a ρ^(r−1)).

Its output has |T|>|S|/2 and actual uncolored grouped energy at most H|T|. Here J is the actual color-type cardinality. The number of pivot/slab groups is not present. `retained_grouped_closing` uses these literal mass and energy forms, setting I=|T| and I₀=|S|=ρδ⁻¹Q.

`SelectedLiftWitness.grouped_attached_sample_energy` supplies the actual lower-energy relation

I² ≤ E² · pivotCount · liftCount · energy,

with E=|occupied| and count arguments

- pivotCount(k,δ,4C,2+2C);
- liftCount(k,δ,2Cδ,4(2Cδ)/κ²,κ³,2/κ).

The new `actual_count_bounds` instantiates the existing proved count bounds with those exact arguments:

Cp(k,C) = (4+2C) (2⌈4C+1⌉+3)^k,
Cl(k,C) = 174 C (2⌈4C⌉+3)^k,
pivotCount ≤ Cp/δ,
liftCount ≤ Cl/κ⁵.

This uses C≥1/2, which is automatic for the actual witness errorConstant(k,width)=width+(k+1)/2 when width≥0. The geometric witness retains its explicit small-scale hypothesis 2Cδ≤κ⁵/4. The common group shifts and center-assigned slab labels cause no extra energy factor.

## Exact closing calculation

From I≥ρδ⁻¹Q/2>0, energy≤HI and the geometric relation, cancel one positive factor I. The resulting coefficient is

c_close = c/[2 Cp Cl 2^(r+1) J] > 0,

and the verified stronger estimate is

E² ≥ c_close κ⁵ A⁻¹ ρ^r δ^(d−d′+1+ε) Q.

For 0<κ≤1 it implies the source's κ⁶ version. The exponent d−d′+1+ε equals the negative of the source's N exponent d′−d−1−ε, because N=δ⁻¹. No integer-exponent restriction is imposed on d,d′,ε,r; all the powers above are real powers. The scalar cancellation itself does not need r≥1, while the actual grouped analytic pruning theorem supplies that hypothesis.

## Density and output substitution

In the scalar density lemmas, n means the projective direction dimension, not the geometric count's ambient dimension k. For the previously proved PivotOutputLowerBound family in ambient k+2, instantiate n=k+1 and the geometric coefficients in dimension k+2.

Use the actual-form population

Q ≥ c_Q κ^(5n) λ⁶ |angles|/[σ²δ²L³],

along with ρ≥c_R κ⁶σ and σ≥c_S λ². For r≥2, the existing proved `KakeyaAudit.Reduction.fiber_density_gain` yields

λ⁶ σ^(r−2) ≥ c_S^(r−2) λ^(2r+2).

The new result is

E² ≥ c_close c_Q c_R^r c_S^(r−2)
      κ^(5n+6r+6) A⁻¹ δ^(d−d′−1+ε) λ^(2r+2) |angles|/L³.

`source_from_energy` specializes r=q+ε, q≥2, ε≥0, reproducing exactly the κ exponent 5n+6(q+ε)+6 and density exponent 2q+2+2ε of (5.34). Its closing estimate is derived internally from raw pruning mass/energy and the count-form geometric witness. For ε≤1 the checked final weakening gives κ^(5n+6q+12)≤κ^(5n+6(q+ε)+6).

To instantiate the earlier actual population theorem, use c_Q=PivotOutputLowerBound.outputCoefficient(k,width)/8, c_S=1/[512·LegalSampleOutputs.outputConstant(k+2,width)], σ=hδ, L=PivotSelectionBudgets.pivotLog δ, and the returned actual P's distinct output cardinality. Its σ bound is strict, hence supplies the non-strict lower bound needed here.

## Proof boundary

`grouped_witness_bound` derives the lower-energy factor from actual AttachedSamples and LegalPositions. `retained_grouped_closing` directly applies it to an actual finite incidence set and occupied endpoint labels; it needs no geometric cardinality or energy lower-bound premise. The pruning upper bound and retained mass are its exact remaining analytic outputs.

`source_from_energy` is the numerical assembly ready for the same concrete data. The remaining full pivot work is constructing and identifying one set of marked outputs, selected lift cells, grouped normalized families, and retained incidence witnesses so every available actual theorem applies to that same set, with the proved ρ≥c_Rκ⁶σ relation and fixed color budget. This module does not claim that assembly or the unconditional final pivot theorem is finished.

## Verification

Lean4.33.1, mathlib commit 0df444a360eaa60ab8c11dca51a86af692955474. Final compile and full-source theorem axiom-audit results will be recorded below.


Final verification: all 13 theorems clean-compiled; the current `.olean` is built; the full-source audit prefix matches the final source; all 13 printed axiom sets contain only propext, Classical.choice, and Quot.sound. No errors, warnings, sorry, or custom axioms occur. SHA-256: `7ea91cf4de666749ae6c389fa42975a079a8eb9f199761132103a02d17c092ff`.

Commands from `audit_work/formalization`:

```
/Users/ssoh/.elan/bin/lake env lean -o .lake/build/lib/lean/ClosingEnergyAlgebra.olean ClosingEnergyAlgebra.lean
/Users/ssoh/.elan/bin/lake env lean ../closing_energy_algebra_axioms.lean > ../closing_energy_algebra_axioms.log
```
