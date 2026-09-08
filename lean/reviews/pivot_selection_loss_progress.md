# Actual pivot output population: exact powers and logarithms

This extension checks and formalizes equations (5.13)–(5.19) of the combined PDF, especially the full actual selection population in (5.19). New files only: `PivotSelectionBudgets.lean` and `PivotOutputLowerBound.lean`. Earlier checkpoints are unchanged.

## Exact dimension and scale conventions

Lean's actual original tube family has ambient dimension n=k+2. Thus the actual projective sphere has dimension n−1=k+1. If h=2^P.level is the common integer fiber size of the constructed selection P and σ=hδ, the lower bound has precisely the two equivalent forms

- Q ≥ c(n,width) κ^(5(n−1)) λ^6 |angles|/[h² δ⁴ L³];
- Q ≥ c(n,width) κ^(5(n−1)) λ^6 |angles|/[σ² δ² L³].

These agree with the source's σ^(-2) N² convention because N=δ^(-1). No κ, λ, δ, h, population, or cap parameter is hidden in c.

## Actual scalar budgets

The verified geometry supplies labelBudget=ceil(PackingConstant·(4·roundingConstant·(1+2width)/κ²)^(n−1)). Define

C_label = PackingConstant·(4·roundingConstant·(1+2width))^(n−1)+1.

Then labelBudget ≤ C_label/κ^(2(n−1)) for 0<κ≤1. Ceiling upward costs a fixed additive coefficient, with no new κ power.

The actual endpoint-label fiber budget is ceil(F/(κδ)), with F=fiberConstant(n,2width)·(1+2width)². Define C_fiber=F+1 and C_log=log₂(C_fiber)+1. Then

- fiberBudget ≤ C_fiber/(κδ);
- Nat.log₂(fiberBudget)+1 ≤ C_log·[log₂(2/(κδ))+2].

The collision-shell logarithm log₂(2/δ)+2 is at most that same κδ logarithm. The explicit output coefficient is

c = 1/[262144·rowConstant(n−2,width)·C_label²·C_log²].

Here 262144=(4·128)², tracking the actual sample population and edge-bin constants. The exponent computation is exact: the square of the label-budget loss contributes κ^(4(n−1)); division by the actual collision energy contributes κ^(n−1), producing κ^(5(n−1)). The sample population squared contributes λ^6 δ^(-6), and the collision denominator returns δ².

## Removing κ from the logarithm

For any fixed natural q, the actual hypothesis δ^q≤κ gives

log₂(2/(κδ))+2 ≤ (q+1)[log₂(2/δ)+2].

Thus only a fixed factor (q+1)³ is lost. In fact the existing geometric collision hypothesis (6width/κ)δ≤1/2 already implies δ≤κ whenever width≥1/12. Consequently the usual fixed widths give the PDF's ordinary δ logarithm with coefficient c/8, without a new polynomial-log assumption. The general theorem with the explicit κδ logarithm allows every width≥0.

## Constructed output, not supplied energy

`PivotOutputLowerBound.construct` invokes the actual geometric collision and label-selection construction. Its returned P is the same `ActualLabelSelection.Selection`: whole most-frequent-second-tube edges, exact original output support, injective selected output representatives, one original angle per output, and exactly h legal original-label triples in every chosen fiber. No desired collision energy, ambient packing bound, output cardinality, or selected-fiber population estimate is an input.

`construct_sigma` additionally proves λ²/(512·outputConstant(n,width))<σ≤C_fiber/κ. `construct_from_two_ends` constructs the legal SampleSystem from the original family's actual all-center ball two-ends tests and then constructs P. Its geometric premises remain explicit: actual admissibility, comparability and separation; nonempty marked transverse angles; the collision smallness condition; and the two legal-sample radius/small-mass conditions. It does not yet select the marked angle population or prove the final pivot estimate. That later assembly remains separate.

## Verification

Development project: `audit_work/formalization`; Lean4.33.1 and mathlib commit 0df444a360eaa60ab8c11dca51a86af692955474. The extension contains 19 theorems: 10 in PivotSelectionBudgets and 9 in PivotOutputLowerBound. Exact full-source audit files append #print axioms for every theorem; their source prefixes are checked against the current modules. Final results are recorded below.


Commands from `audit_work/formalization`:

```
/Users/ssoh/.elan/bin/lake env lean -o .lake/build/lib/lean/PivotSelectionBudgets.olean PivotSelectionBudgets.lean
/Users/ssoh/.elan/bin/lake env lean -o .lake/build/lib/lean/PivotOutputLowerBound.olean PivotOutputLowerBound.lean
/Users/ssoh/.elan/bin/lake env lean ../pivot_selection_budgets_axioms.lean > ../pivot_selection_budgets_axioms.log
/Users/ssoh/.elan/bin/lake env lean ../pivot_output_lower_bound_axioms.lean > ../pivot_output_lower_bound_axioms.log
```

Final verification: both current sources and all 19 theorem audits completed without errors or warnings; no `sorry` or custom axioms. The reported axiom dependencies are only propext, Classical.choice, and Quot.sound.

- `PivotSelectionBudgets.lean`: 10 theorems; current source/audit match; clean built `.olean`; all theorem axioms standard foundations only. SHA-256 `ae81af2f5d51c7665f3d8c97602b48807e8aac9c9db070cb6c5a10813592794d`.
- `PivotOutputLowerBound.lean`: 9 theorems; current source/audit match; clean built `.olean`; all theorem axioms standard foundations only. SHA-256 `3f1ebbef9f24ac065c1d8f5f9eb0a2fd7553a1a031a49a6b1154459719593ad0`.
