# Lifted analytic application: completed bounded phase

`formalization/LiftedAnalytic.lean` contains five proved theorems and four definitions. The main theorem is `KakeyaFormal.LiftedAnalytic.discrete_pruned_lifted_union`.

## Actual conclusion

Fix dimension and exponents with `m,d ≥ 0` and `p,q ≥ 1`, fixed original geometry, fixed slope/error/slab bounds `V,C,b ≥ 0`, and positive losses `epsBase,epsLift`. Assume the two actual estimates

- `DiscreteEstimate (k+1) m d p`;
- `DiscreteEstimate (k+2) d D q`.

There are positive constants `Kbase,cLift` before every configuration, scale, tube count, density, cap coefficient, graph family and pivot. For a finite original family with scale `0 < δ ≤ 1`, actual admissibility/boundedness/cap bound, `A ≥ 1`, and `lam ≤ δ·#shade_i ≤ 2lam`, the theorem constructs the previously verified actual spatial pruning `G`, with a dyadic depth `J ≤ log(1/δ)/log 2` and at least `lam·M/2` incidence mass. Its cutoff is the actual calibrated value

`L = max 1 [Kbase·#F.unionCells·A·δ^(d−m−epsBase)·eta^(−(p+1))·lam^(−p)/M]`,

where `eta = 1/[2(J+1)]`.

For any actual finite graph-shading family `S_i` in dimension `k+2`, the following primitive witnesses suffice: injective original-cell labels in `G.unionCells`, slope bound `‖v_i‖ ≤ V`, common-pivot residual `‖v_i−(pivot−cellCenter δ label_i)‖ ≤ Cδ`, bounded intercepts, actual graph incidences with parameter `t ∈ [−bδ,1+bδ]` and physical error at most `widthLift·δ`, and cumulative original mass `s·N ≤ δ Σ_i #S_i`, with `s ≥ 0`.

Write `P = ceil(1+V)+1`, `B = 4(1+V)^2+2C`, `Csp = PrunedGraphLift.spatialConstant (k+1) width R d`, and `Alift = (Csp·L)·B^d`. The theorem concludes the actual original lifted support estimate

`cLift·Alift^(-1)·δ^(d−D+epsLift)·(s/P)^q·N / (2C+2)^(k+1) ≤ #(⋃_i S_i)`.

Thus the explicit segment loss is `P^q`; the explicit color-count loss is at most `(2C+2)^(k+1)`. No kappa-dependent constant occurs.

## What is constructed rather than assumed

1. Base-estimate heavy-cell pruning and all-radius spatial control are obtained by `PrunedGraphLift.discrete_pruned_graph_lift`.
2. `LiftSegments.normalize_graph_family` constructs one actual Euclidean unit segment and a shading subset for every original graph line. Its per-line incidence loss is at most `P`, while the union is a subset of the original lifted support.
3. The fixed-pivot residual and injective labels imply the actual lifted cap bound and actual residue coloring. Neither cap bounds nor separation are assumptions on the lifted family.
4. Every color is retained and injectively reindexed using `PrunedGraphLift.colorFamily`. The inherited cap bound and proved within-color separation create actual `CumulativeConfiguration` values.
5. The lifted `DiscreteEstimate.to_cumulative` supplies the analytic bound, at the fixed normalization with width `max 1 (widthLift+b(1+V))`, separation `1/[2(1+V)^2]`, and base radius `max 1 (Rlift+V+2)`.
6. The new generic `colored_cumulative_bound` proves the all-color assembly using exact color-size and incidence partitions and the verified finite weighted Jensen theorem. Empty colors contribute zero mass; zero total tube count is handled explicitly.
7. The desired support bound follows from actual union inclusion and the proved number of residue colors.

## Scope and remaining interfaces

The result still assumes the base and lifted discrete estimates: it is the concrete application/implication step, not a proof of either estimate. The geometric graph witnesses remain explicit. It does not construct a favorable global pivot, slab, packet group, graph intercept, incidence assignment, or the lower bound on total lifted incidence from a hairbrush configuration. In particular, `s` records an actual cumulative input inequality and is not asserted to follow from the retained original incidence alone. The original pruning mass and the lifted conclusion are returned together, but they describe distinct incidence families linked by the actual label and graph witnesses.

The theorem has no separation assumption on the original base family, no assumed all-radius ball bound, no assumed normalized lifted family, no assumed coloring, no assumed lifted cap bound, no opaque good-event assumption and no assumed support estimate. Its lifted intercept bound is an explicit fixed geometric input; `LiftSegments.graph_base_from_incidence` is available to derive it from a bounded retained incidence in a later assembly.

The theorem was reviewed for quantifier order, tiny/zero mass, empty colors, the fact that Jensen uses color sizes summing to the original `N`, and preservation of the original lifted support. The fixed parameters `Rlift,widthLift` may be arbitrary real bounds; admissibility/incidence hypotheses enforce the relevant nonempty cases, and the positive normalization uses maxima with one.

## Verification

`lake env lean LiftedAnalytic.lean` and compilation to `.lake/build/lib/lean/LiftedAnalytic.olean` pass. The source contains no `sorry`, `admit` or custom axiom. The theorem axiom printouts report only `propext`, `Classical.choice` and `Quot.sound`. The final compiler output is saved in `audit_work/lifted_analytic_compile.log`.
