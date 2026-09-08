# Full actual separation normalization by finite coloring

`SeparationColoring.lean` contains 23 theorems and 7 definitions. It cleanly compiles and builds in the pinned Lean/mathlib environment. The main theorem's axiom audit is exactly `[propext, Classical.choice, Quot.sound]`; there are no custom axioms or `sorry` terms.

For an actual `TubeFamily (k+1) M` with projectively σδ-separated directions, σ>0 and δ>0, the module constructs a total map from the original indices into a palette of size

`ceil(P_k · (1/min(σ,1))^k) + 1`,

where `P_k` is the previously proved dimension-only projective packing constant. This palette is bounded by `P_k · (1/min(σ,1))^k + 2` and is independent of δ, M, tube positions, density, and cap coefficient A. The theorem is valid for every positive δ, so in particular for the requested interval δ≤1.

The conflict graph is the actual relation `i≠j ∧ projectiveDistance(dir_i,dir_j)<δ`. Its degree bound is derived by applying actual projective cap packing at separation `min(σ,1) δ` and radiusδ. A complete finite greedy-coloring theorem is proved directly by induction on the vertex set: it inserts one vertex, forms the actual set of colors already used by its previously colored neighbors, proves that this set is smaller than the computed palette, and chooses an unused color. No coloring, neighbor cardinality estimate, integrality principle or support bound is assumed.

The main theorem `full_separation_partition F hδ hσ hsep` returns a total coloring such that every reindexed class family is δ-separated, all original arbitrary real tube weights sum exactly over the classes, and the union of all class cell unions is exactly the original union. The class families keep the complete original tube and shading data, reindexed by `Fin` of the actual class cardinality.

Useful interfaces:

- `full_separation_coloring`: the total original-index coloring with same-color δ separation.
- `colorClasses_disjoint`, `colorClasses_cover`, `mem_colorClass`: exact partition, with each tube in precisely its assigned class.
- `classIndex`, `classIndex_injective`, `classIndex_color`, `classIndex_covers`: explicit finite reindexing and original-index recovery.
- `classFamily`: the actual reindexed tube family for each color.
- `classFamily_separated`: target separation of each class.
- `classFamily_cap_bound`: every real-m cap bound passes with the same coefficient A.
- `classFamily_admissible`: the same physical shade-cell admissibility passes to every class.
- `classFamilies_weight_sum`: exact density-weighted or measure-weighted tube summation, valid for arbitrary real weights without equal-weight or positivity assumptions.
- `classFamilies_union`: exact actual full union equality.

No original tube is discarded. Overlap between different color unions is possible, as expected, but their number is bounded by the computed fixed palette. This supports subsequent weighted summation without an unexplained subfamily-retention loss.
