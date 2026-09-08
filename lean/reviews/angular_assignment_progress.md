# Actual cellwise angular incidence and simultaneous tube assignment

Development modules `AngularIncidence.lean` and `AngularAssignment.lean` contain11 theorem declarations each. Both compile cleanly with Lean4.33.1 and Mathlib commit0df444a360eaa60ab8c11dca51a86af692955474. They import the previously verified actual projective geometry and AngularDecomposition.

## Completed result

`KakeyaFormal.AngularAssignment.actual_angular_shading_assignment` starts with an actual finite TubeFamily in ambient dimension d=k+1, M>0, an actual finite collection of original occupied cells, 0<delta≤1 and beta≥0. It constructs one common angular scale tau in [delta,1], a finite global cap net, one assigned cap index for each original tube, and actual finite output shadings in each cap. Set Ck=packingConstant(k)*3^k. The output satisfies:

- all output shadings are subsets of their original tube shadings and of the prescribed original cells;
- a tube can have a nonempty output shading in only its single assigned cap;
- all directions with nonempty shading in a group lie in its actual radius3tau projective cap;
- retained total incidence is at least `3/[8*Ck*(J+1)]` times original cell incidence, where `J≤log(1/delta)/log2`;
- at every original grid cell, every surviving group's actual direction subset is broad with error `4^beta*4Ck` and exponent beta, at every real cap radius r≥delta;
- the number of nonempty angular groups at each cell is at most `2*tau^(-beta)`;
- cells outside the prescribed finite collection have no output incidence, and the broadness/overlap conclusions also hold there.

The output consists of concrete finite grid-cell shadings, so choices keep or remove whole cells. The theorem counts original tube indices and does not drop repeated directions. It does not assume original direction separation, a global angular cover, a good tube assignment, a desired incidence loss, or a broadness-preserving assignment.

The restriction M>0 supplies a fallback net label when selecting global choice functions; the empty family is a trivial separate branch not wrapped into this public theorem. For the manuscript beta≤1, the displayed broadness error is at most16Ck. Constants are independent of scale, tube population, shading density and actual direction locations.

## Constructed geometric and combinatorial inputs

1. `bounded_angular_cap_cover` constructs a maximum-cardinality tau-separated net of actual original directions. Every original direction is within tau of a net center. The previously proved sphere packing theorem bounds the number of radius3tau net caps containing any given direction by Ck. A pointwise radius2tau cap is explicitly placed in one such radius3tau global cap by the projective triangle inequality.
2. `common_scale_cell_pieces` applies actual finite broad-piece selection independently to each original cell and then performs one global weighted scale pigeonhole. The common J is selected before the cells, rather than assuming their individual choices use identical depths. Its retained weighted incidence is at least input/[2(J+1)].
3. `actual_angular_groups` assigns every pointwise piece to a containing actual global cap, regroups those finite sets, and proves exact mass preservation, pointwise disjointness, broadness by summation, and the required bounded number of occupied caps. Each tube occurs in at most Ck global angular groups because all of those caps contain its actual direction.
4. `weighted_group_assignment` constructs an actual maximizing group for every original tube, using its real whole-cell shading count as weight. Summation over active groups proves the reciprocal Ck mass loss. Exact finite incidence double counting transfers this tube-wise statement to the actual group/cell incidence array.
5. The subsequent explicit threshold retains a cell only when its assigned subset has at least1/(4Ck) of that group's former incidence. The summed discarded assigned mass is at most one quarter of post-assignment mass. The proof does not infer pointwise broadness directly from the maximum-weight assignment: it uses the proved proportional-subset broadness theorem after this deletion.
6. `restoredShading` constructs the actual finite output shades. Its incidence identity and total-cardinality identity prove that the final statements refer to those shades rather than an abstract surrogate mass. Unique group assignment is proved from actual surviving membership.

## Comparison with the PDF and remaining work

This closes the finite whole-cell angular grouping and simultaneous tube-to-angular-cap assignment part of Section3.2. The finite argument avoids two extra preliminary pigeonholes used in the presentation, so the angular-only phase proves an explicit single-logarithm retention; this is not a claim that every later step of Lemma3.2 is already formalized. The fixed pointwise/mass/overlap conclusions needed here are proved directly.

Spatial grouping remains separate: assigned tubes must be placed in actual parallel spatial covering tubes, then split into spatial pieces and proportionally restored again. The bounded-overlap spatial cover, its compatibility with angular broadness, and anisotropic angular rescaling are not conclusions of these modules. The entire continuous measurable version and the final analytic application also remain separate. An actual finite-cell result should not be described as a proof of all of Lemma3.2 before those interfaces are complete.

## Verification

From audit_work/formalization:

```
/Users/ssoh/.elan/bin/lake env lean -o .lake/build/lib/lean/AngularIncidence.olean AngularIncidence.lean
/Users/ssoh/.elan/bin/lake env lean -o .lake/build/lib/lean/AngularAssignment.olean AngularAssignment.lean
/Users/ssoh/.elan/bin/lake env lean ../angular_incidence_axioms.lean > ../angular_incidence_axioms.log
/Users/ssoh/.elan/bin/lake env lean ../angular_assignment_axioms.lean > ../angular_assignment_axioms.log
```

The audit sources append#print axioms for all11 declarations in each exact module. Axiom checking permits only the standard foundations propext, Classical.choice and Quot.sound. Neither module introduces sorry, admit, native_decide, a custom axiom or an unproved selection/covering oracle.
