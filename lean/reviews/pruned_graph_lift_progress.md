# Actual pruning-to-fixed-pivot graph lift interface

`PrunedGraphLift.lean` connects the constructed spatial pruning to actual normalized graph directions. It does not assume a generic spatial all-radius bound or the desired lifted cap conclusion.

The actual original admissibility and bounded tube bases imply every original shading cell center lies in the ball about zero of radius `R0=max(0,R)+1+width`, for δ≤1 and nonnegative width. For the actual survivor family G, the original unit-scale coarse fibers give a total-count bound `|union G| ≤ coverConstant(n,R0) L δ^(-d)`. Combining this with the already proved δ≤rho≤1 pruning bound extends it to every rho≥δ:

`#(union G ∩ ball(x,rho)) ≤ Csp L (rho/δ)^d`,

where `Csp=max(coverConstant(n,1)·2^d, coverConstant(n,R0))`. This includes arbitrary ball centers and all radii required by the graph-cap theorem.

The main `discrete_pruned_graph_lift` obtains the pruning constant K from the actual base estimate before every configuration. It constructs the same logarithmic depth J, explicit cutoff L, and actual G as PrunedIncidence. Its output retains unchanged original tubes, actual subset shadings, union containment, and normalized incidence at least `λM/2`, together with the all-radius spatial estimate.

For every actual lifted family T and legal fixed-pivot witnesses:

- slopes v_i satisfy `||v_i||≤V`;
- actual labels are injective and belong to `G.unionCells`;
- the actual residual satisfies `||v_i−(pivot−cellCenter δ label_i)||≤Cδ`;
- T's actual directions equal the normalized graph directions of v_i;

the theorem derives

`T.CapBound δ d [(Csp L)·(4(1+V)^2+2C)^d]`.

It simultaneously constructs every residue color, with modulus `0<Q≤2C+2`, and separation `δ/[2(1+V)^2]` between any distinct lines of the same color. The available color count is at most `(2C+2)^n`. No color is selected or discarded. The actual per-color `colorFamily` reindexing inherits cap and separation, and an exact finite double-counting theorem proves that all color families together retain every original shading incidence exactly once. The cap coefficient is also proved ≥1 when L≥1, meeting the normalized cumulative-input requirement.

All factors beyond the actual pruning cutoff depend only on n, width, R, the fixed slope bound V and fixed residual bound C. There is no kappa parameter or conditioning loss inserted into the cap/color constants. Calling these constants independent of kappa presumes, as in the manuscript, that the supplied V and C are fixed bounds independent of kappa.

Remaining interface: the residual, actual label membership/injectivity, bounded slopes and graph directions are explicit geometric witnesses. This theorem does not manufacture them from endpoint/output selection, nor assert any lower bound on the number of lifted lines from the base retained mass. Unit-segment admissibility and boundedness of T must still come from the existing graph slab/segment construction. Those are not hidden cap or spatial-count assumptions.
