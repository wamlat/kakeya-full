# One uniform scale threshold for actual pivot geometry

`PivotGeometryScale.lean` provides a single concrete fixed coefficient

    T=max(1,12w,4 roundingConstant(n,w)(1+2w),8 errorConstant(n,2w)).

If T ≤ delta^-1 (kappa/(1+2w))^20, the theorem derives all original and normalized scale conditions needed by the actual collision, selected slab and attached witness modules. These include delta ≤ kappa/(1+2w), the original collision bound, the original output noncollapse bound, and both fifth-power normalized slab/lift perturbation bounds. Original and normalized meshes are kept distinct.

The original manuscript cutoff follows with the fixed factor (1+2w)^20. The theorem `uniform_choice_tests` supplies one delta0>0 before later configurations, B or K are chosen, assuming their explicit fixed polynomial-logarithmic budgets. It applies the actual PivotKappa.choice and the existing uniform scale theorem; kappa positivity and its bound by one are derived.

All four source theorems and all 21 local theorem declarations, including the generated record declarations, compile and pass a full-source axiom audit. Dependencies are only propext, Classical.choice and Quot.sound; there are no compiler diagnostics or custom axioms. Final uniform pivot assembly must still supply the stated logarithmic coefficient budgets from its actual prior reductions.
