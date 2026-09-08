# Cap-free maximal shading predicates

`MaximalShading.lean` is a new frozen generic interface module. It distinguishes the fixed bounded-base normalization (`MaximalShading.BoundedEstimate n d`) from the literal arbitrary-position assertion (`MaximalShading.Estimate n d`). Both use the exact sum of actual radius-δ unit-tube volumes and arbitrary measurable shadings of relative density at least λ, with 0<δ,λ≤1. Both have the manuscript's power δ^(n−d+epsilon) λ^d and fixed positive projective direction separation. Neither predicate assumes a cap condition or carries an original cap coefficient A.

`Estimate` quantifies the fixed positive direction separation first, then epsilon and its constant, before all actual tube families, positions, scales, densities, populations, and measurable shadings. It has no bounded-base premise. `BoundedEstimate` quantifies the existing positive radius/separation normalization before epsilon and its constant, and explicitly includes that base bound.

`bounded_maximal_of_volume` derives BoundedEstimate(k+1,d) from the existing proved VolumeMeasurableEstimate(k+1,k,d,d). The ambient cap condition is derived by `ProjectiveGeometry.separated_tube_family_cap_bound`; its cap coefficient depends only on fixed separation and dimension. Thus its inverse is absorbed in the fixed constant. This closes the cap-premise mismatch with the manuscript's maximal formula without invoking a published-result axiom.

This module does not claim that bounded implies unbounded, nor assert any new numerical exponent. The actual arbitrary-position measurable spatial reduction is being implemented separately. The six-dimensional specialization imports this module without circular dependency.

Build and audit:

```
lake env lean -o .lake/build/lib/lean/MaximalShading.olean MaximalShading.lean
lake env lean ../maximal_shading_axioms.lean
```

Both produced zero diagnostics. The exact full-source copy was audited using the production all-local-declaration collector. Only propext, Classical.choice and Quot.sound occur; no sorry, admit, custom axiom, unsafe, or native_decide appears in source. Exact hash and declaration counts are in `maximal_shading_audit.json`, with full evidence in `maximal_shading_axioms.lean` and `.log`. Lean4.33.1, mathlib `0df444a360eaa60ab8c11dca51a86af692955474`.
