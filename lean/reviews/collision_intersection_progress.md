# Actual grid intersection counts for the collision row

`CollisionIntersection.lean` is complete, clean-compiled, built, and frozen: 11 theorems and one definition. Its separate audit checks all 12 declarations, with only the standard foundational axioms and no placeholders.

In ambient dimension n and width w≥0, set

C(n,w) = 16(1+w)(6+4w)(2 ceil(w+1)+3)^n.

`common_cell_count` proves that any actual finite set of original mesh-δ centers in both radius-wδ unit tubes T,S has cardinality at most C(n,w)/θ whenever 0<θ≤projectiveDistance(T,S). The proof enlarges only the auxiliary diameter calculation to positive width (1+w)δ, invokes the proved actual two-point tube intersection diameter, and uses original-width tube/ball grid packing. It uses no volume-to-cardinality inference. Width zero and empty intersections are included.

The configuration-facing forms are:

- `common_shading_count`: |shade_i ∩ shade_j| ≤ C(n,w)/φ at any positive lower angle φ, in particular in every shell δ≤φ≤1.
- `common_label_subset_count`: the same bound for any actual subset of those common labels.
- `common_vertex_count`: |H ∩ shade_i ∩ shade_j| ≤ C(n,w)/(2κ) at the actual marked-angle threshold 2κ.
- `fixed_pair_angle_count`: the actual original marked-angle set with first index i and second index j has at most C(n,w)/(2κ) elements. The separation follows from nonempty membership in the constructed angle set; no additional angle hypothesis is assumed. `fixed_pair_vertex_injective` proves that vertex labels determine these fixed-index angles, preventing duplicate witnesses from inflating the count.
- `fixed_pair_angle_subtype_count`: exactly the same statement on the angle subtype used by the output/edge modules.

The bottom shell is covered explicitly: `common_cell_count_max` and `common_shading_count_max` give C(n,w)/max(projectiveDistance,δ) for 0<δ≤1. These include a tube paired with itself and projective distances below δ. Their proof uses actual whole-unit-tube grid packing for that case. Thus the subsequent collision-row sum can use φ=δ for the lowest shell without falsely requiring positive separation there.

These are the original intermediate-label and vertex-label factors between (5.17) and (5.18), physical PDF page 20. The fixed-intermediate pivot-label factor C/δ remains in `PivotOutputCount`. Assembly of the finite collision row and dyadic summation remains separate.
