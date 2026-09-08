# Actual spatial geometry, proportional splitting and finite angular–spatial decomposition

Three development modules compile cleanly with Lean4.33.1 and Mathlib commit0df444a360eaa60ab8c11dca51a86af692955474:

- SpatialAngular.lean:14 theorem declarations;
- SpatialSplitting.lean:7 theorem declarations;
- SpatialAssignment.lean:8 theorem declarations.

## Completed combined theorem

`KakeyaFormal.SpatialAssignment.discrete_angular_spatial_decomposition` starts from an actual finite TubeFamily in ambient dimension d=k+1, M>0, whole-cell shadings with admissibility width*delta, bounded original tube bases by R, a prescribed finite subset of its occupied cells, 0<delta≤1, width≥0 and beta≥0. It constructs a common angular scale tau∈[delta,1], finite angular and spatial labels, actual finite output shadings, and a single angular assignment for each tube. Every nonempty output shading belongs to exactly that tube's assigned angular cap and its uniquely determined spatial lattice label.

Define

`Ck = packingConstant(k)*3^k`,

`B(k,width) = [2*ceil((k+width+3)/2)+3]^k`.

The output guarantees:

- each output shading is a subset of its original tube shading and of the prescribed original grid cells;
- nonempty output tubes have directions in their group's actual radius3tau projective cap;
- every such tube's entire actual width*delta carrier lies in its assigned parallel spatial box;
- the box has longitudinal interval of length2*(R+1+width), with its transverse radius exactly(k+width+3)*tau;
- retained incidence is at least `9/[32*Ck*(J+1)]` times input incidence, where `J≤log(1/delta)/log2`;
- every group's surviving actual direction subset at each grid cell is broad with exponent beta and error `4^beta*16*Ck*B(k,width)`, for every real cap radius r≥delta;
- the number of occupied angular–spatial groups at each cell is at most `2*B(k,width)*tau^(-beta)`.

All statements are for actual original tube indices and actual finite grid-cell shadings. The theorem does not assume original direction separation, a desired broad decomposition, a bounded-overlap cap/spatial cover, a good assignment, or a mass-retention conclusion. Geometry and finite selection are constructed from the supplied tube family. For the manuscript's beta≤1, the broadness error is uniformly at most64*Ck*B(k,width).

## Spatial geometry proved directly

The spatial frame is the explicit orthogonal Householder map aligning a group's unit direction with the first coordinate axis. The tail projection is a contraction. For every direction v, its transverse norm is bounded by the actual unoriented chord distance to the group direction; both projective sign branches are proved.

Each original tube receives the integer label of its base's transverse projection on a grid of side2tau. The base-to-grid-center error is at most k*tau. Unit-length motion contributes at most3tau transversely because its direction belongs to the radius3tau cap; the original carrier contributes at most width*delta≤width*tau. This proves containment of the entire endpoint-capped original tube in the explicit lattice-axis cylinder of radius(k+width+3)*tau.

At any physical point, distinct cylinder labels have actual transverse grid centers within that radius. The previously proved integer-grid ball count gives B(k,width), with no assumed axis-overlap property. For discrete incidences the point is the actual fine-cell center, justified by the original admissibility witnesses.

A bounded original base implies every actual carrier point has norm≤R+1+width. Its aligned longitudinal coordinate therefore lies in the fixed interval [−(R+1+width),R+1+width]. `matching_axis_distance` proves that transverse distance is exactly distance to the matching actual point of the parallel lattice axis. `parallelBox_axis_segment` identifies the finite axis interval explicitly; these are finite-length covers rather than infinite cylinders being silently used as bounded tubes.

The actual transverse map `normalizeBox` divides transverse offsets by tau while leaving the longitudinal coordinate intact. The theorem `normalizeBox_width` proves its image has a fixed transverse width and longitudinal bound. No claim of a completed transformed unit-direction/cap/volume theorem is made from this elementary normalization fact alone.

## Proportional spatial splitting

The actual label fibers partition each angular parent's pointwise direction-index set. At most B labels are occupied. Keeping a fiber only if it contains at least1/(4B) of its parent loses at most one quarter of that parent's population at each point. Thus the spatial loss is pointwise, not merely a global unweighted estimate. Retained fibers inherit broadness from the parent with the factor4B. All choices retain or delete whole original grid cells.

The code builds finite output shadings and proves exact incidence double-counting identities connecting their cardinalities to the pointwise restored fibers. Total retention is therefore a statement about those actual shadings, not an abstract mass proxy. The spatial-overlap bound is summed only over originally active angular parents, preserving the tau^(−beta) power without introducing a new delta power.

## Exact remaining scope

The combined theorem establishes the finite-cell angular/spatial decomposition properties with explicit bounded-length parallel boxes. Its stronger single-logarithm retention comes from the direct finite pointwise construction used in AngularDecomposition, and does not claim that every later density restoration or analytic application avoids the other manuscript losses.

Three interfaces remain separate:

1. A full anisotropic angular rescaling theorem must transform actual tube segments, normalize their direction speeds/lengths, control the real cap coefficient and shadings, and account for volume/grid rounding. `normalizeBox_width` alone does not establish this.
2. The actual arbitrary-measurable shading version needs measurable incidence-pattern atoms and real atom weights in the global angular radius/assignment steps. Spatial restoration is already pointwise and compatible with weighting, but the full weighted/angular bridge is not silently inferred here.
3. The nonempty-family assumption M>0 supplies the angular-net fallback label. The empty-family branch is trivial but not wrapped into the final public theorem. The analytic seed/pivot/induction and mass-retaining pruning remain independent work.

The coarse boxes have fixed longitudinal length depending on R and width; they are not asserted to be exactly the preexisting UnitTube.carrier with segment length1. Passing those bounded lengths into a preferred normalization requires the usual explicit fixed-factor normalization interface.

## Reproducible verification

From audit_work/formalization, for each of SpatialAngular, SpatialSplitting and SpatialAssignment:

```
/Users/ssoh/.elan/bin/lake env lean -o .lake/build/lib/lean/NAME.olean NAME.lean
```

Full-source axiom audit files/logs are `spatial_angular_axioms`, `spatial_splitting_axioms` and `spatial_assignment_axioms` in audit_work. They append#print axioms for all14/7/8 respective declarations and check that only propext, Classical.choice and Quot.sound occur. No sorry, admit, native_decide or custom axiom is introduced.
