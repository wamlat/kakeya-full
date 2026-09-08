# Actual cumulative arbitrary-shading estimate

`CumulativeEstimate.lean` compiles with Lean 4.33.1 and the pinned mathlib checkout; the exported theorems use only `propext`, `Classical.choice`, and `Quot.sound`. No `sorry`, custom axiom, or assumed dyadic decomposition appears.

The new `CumulativeConfiguration` contains actual Euclidean unit tubes and finite grid-cell shadings, the same admissibility, separation, boundedness and real cap condition as the normalized discrete estimate, and only the cumulative mass condition `s M ≤ δ Σ_i #shade_i`. Every individual shading may be empty. `s` is any nonnegative real; no positive lower bound, or density comparability, is imposed. The empty family is included.

`DiscreteEstimate.to_cumulative` proves the corresponding uniform estimate for every real power `p ≥ 1`. Its constant is chosen before δ, s, A, M, or the configuration. The real-cap dimensional wrapper is also proved.

The proof constructs actual equal-cardinality subsets and injectively reindexed tube subfamilies, uses the already proved geometric `C(k,width)/δ` count bound, and applies genuine normalized configurations with density at least `δ K/(2C)`. Thus it correctly handles raw integer counts exceeding `1/δ` without silently imposing density ≤ 1 on an invalid configuration.

Positive integer counts are classified by their actual binary logarithm, and an explicit zero-density class contains empty shadings. The class densities have weighted total at least `s M/(4C)`. Weighted Jensen preserves the original real power p and incurs one factor equal to the number of classes. The class budget is controlled by `log(C/δ)`, then absorbed uniformly into any requested positive scale loss. In particular no `log(1/s)`, cap coefficient, or tube-count term enters the loss.

Independent statement audit within this phase: checked the zero-mass branch, positivity of every divided constant, inheritance of cap bounds under selected indices, the integer-bin endpoints, the upper-count dependence, and the order of uniform quantifiers. This is a conditional consequence of `DiscreteEstimate`; it does not assert a new unconditional Kakeya estimate.
