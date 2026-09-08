# UniformPrunedPivotSelection

Status: clean Lean compilation with all local axiom checks equal to `propext`, `Classical.choice`, and `Quot.sound`. The entire two-theorem source was inspected. There are no `sorry`, `admit`, custom axioms or unsafe declarations. The dependency `PrunedPivotSelection` was separately compiled and reviewed, and the imported uniform cutoff comes from the parent's audited `PivotGeometryScale` and actual logarithmic lower-bound argument in `PivotKappaScale`.

`recovered_geometry` uses the correct recovered two-ends coefficient 2B. Given fixed width, positive B0 and K0, positive alpha and nonnegative b,q, it chooses a single delta0 in (0,1] BEFORE later delta, B or theta. For 0 < delta <= delta0, B >= 1, 0 < theta <= 1 and

    B <= B0 log(2/delta)^b,
    theta^(-1) <= K0 log(2/delta)^q,

it derives all actual `PivotGeometryScale.Tests` for kappa = choice(width, 2B, theta^(-1), alpha, 1). The fixed B budget supplied to the uniform theorem is 2B0, not B0. The lower bound 1 <= theta^(-1) follows from theta in (0,1]. In particular, both the original collision test and the post-homothety attached-sample/slab tests follow with the original and normalized meshes kept distinct.

`construct` chooses both the pruning constant K and delta0 before the original family, comparison set, original marks, density, cap coefficient, marked fraction, B and theta. It then constructs literal spatial pruning, actual marked recovery with the injective original index map, actual legal sample system S and actual whole-edge selection P. It preserves every conclusion of `PrunedPivotSelection.construct` and also returns all geometric Tests. The explicit collision-smallness premise of the preceding module has been discharged rather than hidden in a renamed hypothesis.

The output bound remains

    Q >= (outputCoefficient/65536) kappa^(5(k+1)) xi^2 lambda^8 M^2
         / (sigma^2 delta^4 pivotLog(delta)^3 |E|),

with the proved sigma range, original M and E, and Q the literal distinct retained output support. The scale threshold may depend on fixed dimension, width, alpha and the stated logarithmic budget constants/exponents. It is independent of later B,theta,xi,delta,A,lambda and the family.

Remaining assumptions are substantive and explicit: the base DiscreteEstimate, the original admissibility/separation/boundedness/cap/comparable-density hypotheses, fixed-theta broad marks of mass at least xi lambda M/delta, original full two-ends control, and the quantitative logarithmic budgets. The theorem applies to delta <= delta0; a final estimate across all delta still needs its separate coarse-scale branch. This module does not claim to derive those logarithmic budgets from localization/sampling or to close the grouped lifted analytic and energy assembly downstream.

Compile log: `uniform_pruned_pivot_selection_compile.log`.
