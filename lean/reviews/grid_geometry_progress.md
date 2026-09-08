# GridGeometry: actual Euclidean grid counting

## Completed

`audit_work/formalization/GridGeometry.lean` imports the concrete definitions in `Configurations.lean`: `Space k = EuclideanSpace ℝ (Fin k)`, `Cell k = Fin k → ℤ`, the actual scaled center `cellCenter δ z`, and unit-direction `UnitTube`. The results below are genuine geometric counting conclusions; none assumes a grid counting estimate or covering conclusion.

- `gridBox` is an explicit finite integer coordinate box. Its cardinality is proved exactly: `(2*n+1)^k` for coordinate radius n.
- Euclidean distance bounds each coordinate difference, and positivity of δ permits division by the actual mesh size.
- A Euclidean ball centered at arbitrary x with physical radius R*δ lies in the explicit integer box of radius `ceil(R)+1` around the coordinatewise integer floors of x/δ. Consequently every finite set of its cell centers has cardinality at most `(2*ceil(R)+3)^k`.
- For R≥0 this is at most `5^k*(1+R)^k`, proved over the reals. The constant is explicit and depends only on ambient dimension.
- A tube portion parameterized over `[a,a+L*δ]`, L≥0, with actual distance at most width*δ from its unit-speed axis is contained in a ball of radius `(width+L)*δ`. Thus its cell count is at most `(2*ceil(width+L)+3)^k`. In particular, each longitudinal interval of length δ has a count bounded independently of scale and tube position.
- A proved mesh selection on [0,1] produces at most `ceil(1/δ)+1` sample parameters. Each admissible unit-tube cell belongs to an explicitly constructed union of boxes around those samples. Therefore its count is at most `(ceil(1/δ)+1)*(2*ceil(width+1)+3)^k`, a bound linear in `1+1/δ`. A real-valued version bounds it by `2*(2*ceil(width+1)+3)^k*(1+1/δ)`.
- `admissible_shade_card_bound` connects this result directly to the existing `TubeFamily.Admissible` definition.
- The mesh argument is extended to an arbitrary segment between actual Euclidean endpoints x,y, including coincident endpoints. `segment_grid_count` gives `(ceil(dist(x,y)/δ)+1)*(2*ceil(width+1)+3)^k` for every finite population of cell centers within width*δ of that segment. `segment_grid_count_of_length_le` substitutes any upper bound D for the segment length.

## Interfaces for other modules

All theorem names lie in namespace `KakeyaFormal.GridGeometry`.

```lean
ball_grid_count hδ x cells hball
ball_grid_count_real hδ hR x cells hball
longitudinal_grid_count T hδ hL cells hinc
one_mesh_interval_grid_count T hδ cells hinc
unit_tube_grid_count T hδ cells hinc
unit_tube_grid_count_real T hδ cells hinc
segment_grid_count x y hδ cells hinc
segment_grid_count_of_length_le x y hδ hD cells hinc
```

The segment hypothesis uses Mathlib's actual `segment ℝ x y`, not an opaque segment-membership predicate. Geometry_audit has been sent these interfaces for the endpoint-triple pivot-support module.

## Scope and remaining work

This closes the elementary physical-grid counting interface used when cells are shown to lie near a ball, a short longitudinal interval, a unit tube or an endpoint segment. Neither tube-grid alignment nor a special direction is assumed.

It does not itself establish that a projected/lifted pivot configuration meets a particular ball or segment constraint, control projection operator norms, prove direction-cap counting, or prove the main maximal estimate. Those require the other geometric and analytic modules. The constants here are explicit upper bounds; no attempt is made to optimize them.

## Reproduction

From `/Users/ssoh/Documents/Codex/2026-09-06/work/audit_work/formalization`:

```sh
/Users/ssoh/.elan/bin/lake env lean -o .lake/build/lib/lean/GridGeometry.olean GridGeometry.lean
```

This completed with exit0 and no warnings or errors. Toolchain: Lean4.33.1 and Mathlib commit `0df444a360eaa60ab8c11dca51a86af692955474`. The source uses no `sorry`, `admit`, `native_decide` or custom axioms. `audit_work/grid_geometry_axioms.lean` copies the source and requests `#print axioms` for every theorem; its output is recorded in `audit_work/grid_geometry_axioms.log`.

The file contains 19 theorem declarations. Every completed axiom report uses only `propext`, `Classical.choice`, and `Quot.sound`; no `sorryAx` or custom axioms occur.
