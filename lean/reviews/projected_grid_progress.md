# Actual projected-grid geometry for the source Lemma 2.1 route

Both new modules are frozen, clean-compiled and exact-source audited PASS:

| Module | SHA256 | Named theorems | Theorem declarations | All declarations |
|---|---|---:|---:|---:|
| ProjectedGrid | 7ce2f4373b7ff11280775ead5eed783ef76599fa3d3c69861696babb11807faa | 6 | 8 | 11 |
| ProjectedGridFamily | 92744d3882fc76cb440fb5ffcecab5757adb2857fa371d8a986bfbba3d6d532f | 10 | 19 | 22 |

All 33 local declarations have only standard foundational axiom dependencies. There are no custom axioms, sorry/admit/native_decide, warnings or errors. The audit checks the exact complete source with the production all-declaration audit appended, including proof-bearing definitions and every named source theorem. See `projected_grid_audit.json`, `ProjectedGrid_SourceAudit.log` and `ProjectedGridFamily_SourceAudit.log`.

The construction is generic in source dimension n and target dimension d; the source application is n=7,d=5. Its input is an actual continuous linear map P with ||P||<=K, mesh delta>0, an actual original unit-axis family with center admissibility of width*delta, and actual projected-direction norms at least c>0. Fixed K,c,width and dimensions determine every fiber constant before the mesh, family, shading, population or density. There is no desired output geometry, projected count, fiber bound, or projected density hypothesis.

The common map is literally

    labelMap P delta z = GridCells.label delta (P (cellCenter delta z)).

It is independent of the tube index. The half-open grid labeling fixes all boundary choices. Its rounding error is at most d*delta/2; two old centers with the same target label have projected images at distance at most d*delta.

For two original cells on one source tube, actual center errors from that tube axis are at most width*delta. The previously proved continuous-linear-map parameter lemma then gives longitudinal separation at most ((d+2*K*width)/c)*delta. Returning to the original centers gives distance at most R*delta, where

    R = 2*width + (d+2*K*width)/c.

Every nonempty actual map fiber is therefore contained in a ball about one of its own original centers. The existing explicit integer-box ball count proves its cardinality at most

    C = (2*ceil(R)+3)^n.

The empty-fiber case is treated directly. No grid covering or count estimate is assumed. The exact finite fiber-sum identity yields card(S)/C <= card(image S) for each original row.

`ProjectedGridFamily.family` uses the same original tube indices, image rows under this one map, base P(base_i), and normalized direction P(v_i)/||P(v_i)||. The actual physical length is ||P(v_i)|| and lies in [c,K]. The axis-image identity is exact at the reparametrized parameter t*||P(v_i)||. Every target shading center lies in the actual corresponding lengthCarrier with radius (K*width+d/2)*delta. This includes both the image of the original transverse error and the target rounding error. A bounded old base family remains bounded with factor K.

The final `construct` theorem produces an actual target TubeFamily and proves all these identities and inequalities. In particular its finite union is exactly the image of the original finite union, so its cardinality is at most the original cardinality with constant ONE. This stronger count applies to the chosen center-image shadings; the theorem does not assert that one target cell covers the full geometric image of an entire old cell. No such coverage is necessary for these actual admissible finite shadings and their count bound.

Each actual target row has count between old_count/C and old_count. `density_bounds` specializes this to original Comparable(delta,lambda), giving lambda/(C*delta) <= target_count <= 2*lambda/delta. Thus only a fixed density comparability factor is lost. There is no padding, independent resampling, repeated image multiplicity in the finite set, or selection oracle in the target family.

This proves the continuous/grid geometric content at combined.txt lines255–266: bounded projected lengths, bounded transverse width, fixed collapse multiplicity and comparison of projected and original union counts. Direction separation is deliberately not inferred for an arbitrary linear map. The actual normalized direction formula is exposed so a subsequently chosen collision-free original subfamily can provide separation; the Gaussian collision graph and its independent-set selection are separate source steps. The source Wolff estimate is also a separate analytic input. These two modules do not by themselves claim the complete Lemma 2.1 projection proof.

Commands, run in `audit_work/formalization` with the pinned matching Lean/mathlib dependencies:

```sh
lake env lean -o .lake/build/lib/lean/ProjectedGrid.olean ProjectedGrid.lean
lake env lean -o .lake/build/lib/lean/ProjectedGridFamily.olean ProjectedGridFamily.lean
python3 ../audit_projected_grid.py
```

This is an individually audited source checkpoint. The parent handles integrated publication, source-statement inventory, and the remaining collision/selection/analytic assembly.
