# Actual lifted graph geometry

`LiftGraph.lean` now proves the actual normalized graph chart, fixed-pivot cap control and separation coloring. `LiftSegments.lean` proves actual Euclidean unit-length covers and normalization of finite graph shadings. Both individually compile cleanly; package-wide verification is scheduled for the next checkpoint.

The distinguished graph coordinate is written first as `(1,v)`; an orthogonal coordinate permutation gives the manuscript's last-coordinate convention. For slopes of norm at most V, actual projective chord distance satisfies

`pd(graph(v),graph(w)) ≤ 2||v-w||`,

`||v-w|| ≤ 2(1+V)^2 pd(graph(v),graph(w))`.

The inverse inequality treats the antipodal branch explicitly. For actual injective grid labels and the common-pivot residual `||v_i-(z-cellCenter(delta,label_i))||≤C delta`, every radius-r graph cap confines those labels to a genuine spatial ball of radius `(4(1+V)^2+2C)r`. Substituting the actual pruned spatial ball bound gives the concrete TubeFamily cap predicate, with coefficient `F*(4(1+V)^2+2C)^d`. These constants depend only on fixed slope/error ranges and carry no inverse conditioning power.

Residues modulo Q=ceil(2C+1) give Q^k explicit colors, with Q≤2C+2. Keeping every color retains all lines. Distinct indices of the same color have actual graph-direction separation at least `delta/[2(1+V)^2]`; the proof derives their lattice coordinate gap and then uses the common-pivot residual.

A graph parameter slab of length one is covered by at most ceil(1+V)+1 genuine Euclidean unit segments. The cover is derived from the arc-length floor. Parameters extending by b delta beyond a slab boundary enlarge width from width to width+b(1+V). A retained point in a fixed region controls the translated graph intercept, and each resulting unit piece has fixed bounded geometry independent of the original slab index.

`normalize_graph_family` constructs per-line unit-piece assignments and subshadings. Every line remains; each shading retains at least its original cardinality divided by ceil(1+V)+1; the union decreases; actual admissibility, direction equality and bounded bases are proved. Subsequent density trimming and applying an analytic estimate remain separate, as do the globally selected output-fiber labels and their retained incidence mass. No full pivot or lifted analytic estimate is claimed by these geometry modules.
