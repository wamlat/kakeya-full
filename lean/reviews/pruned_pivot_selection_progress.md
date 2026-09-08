# PrunedPivotSelection: original marked input to actual selected outputs

Status: complete, frozen for integration. `PrunedPivotSelection.lean` compiled to its local `.olean` with no warnings on Lean 4.33.1 and the project's pinned Mathlib. All three local theorems were individually inspected and their printed axiom sets are exactly `propext`, `Classical.choice`, and `Quot.sound`. No `sorry`, `admit`, custom axiom, or unsafe declaration occurs in the source. Compile log: `pruned_pivot_selection_compile.log`.

## Genuine construction

`construct` first invokes actual spatial deletion at loss xi/100, then actual marked recovery, and finally the original-cell legal-sample and collision selection theorem. Its constant K is chosen before all original configurations, marked fractions and scale-dependent coefficients. It returns the literal pruning depth J, threshold L and original pruned family O, including the actual deletion and small-radius ball bounds. The returned `RecoveredInput` retains an injective map into the original tube indices, full shadings equal to the literal pruned shadings at those indices, marked shadings contained in both recovered full and original marked shadings, and density equal to either lambda/2 or lambda.

It then returns the actual dependent legal `SampleSystem S` and whole-edge `Selection P`. There is no assumed angle population, sample count, output count, geometric collision energy or abstract cumulative estimate in this composition. Those facts come from the imported proved constructors. The base `DiscreteEstimate` remains an explicit hypothesis, used to produce the spatial pruning.

Writing sigma = 2^(P.level) delta and kappa = choice(width, 2B, theta^(-1), alpha, 1), the original-parameter conclusion is

- sigma > lambda^2 / (2048 outputConstant),
- sigma <= fiberCoefficient / kappa,
- Q >= (outputCoefficient / 65536) kappa^(5(k+1)) xi^2 lambda^8 M^2 / (sigma^2 delta^4 pivotLog(delta)^3 |E|),

where Q is the cardinality of the actual retained distinct-output support. The 65536 is checked by exact field/ring normalization: 16 from the existing output theorem, 64 from the recovered density's sixth power, and 64 from the square of xi lambda M/(8 delta). The lower sigma loss is the recovered density's squared factor four. E and M in this bound are the original comparison set and tube count, not the recovered family count. Positivity of E is derived in marked recovery.

## Hypotheses and limits

The original finite family must be admissible, separated at delta, uniformly bounded, satisfy the original cap bound and comparable full density, and have marked mass at least xi lambda M/delta. Marks satisfy the fixed-radius theta cap bound with fraction 1/10, and full shadings satisfy the original two-ends bound with B >= 1 and alpha > 0. Width >= 1/12 is retained from the actual legal-output selection theorem. The original comparison set E is an actual finite cover of all original shadings.

The theorem still explicitly requires delta in (0,1] and the collision condition (6 width/kappa) delta <= 1/2. `geometry_tests` proves that the single sufficient original-scale cutoff geometryConstant (1+2 width)^20 <= delta^(-1) kappa^20 supplies this condition and all listed normalized-lift perturbation tests. The choice correctly uses the recovered two-ends coefficient 2B. A follow-on module will derive this cutoff uniformly from quantitative polylogarithmic bounds on B and theta^(-1); no claim of unconditional smallness or a completed pivot theorem is made here.

Full-source mathematical review found no circular premise or cardinality substitution. The final selected lift geometry and grouped lifted analytic/energy assembly remain downstream interfaces.
