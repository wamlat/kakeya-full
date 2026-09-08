# Independent finite-agent review: CollisionIndependentSet

Read-only mathematical review of every statement and proof in frozen `CollisionIndependentSet.lean`, SHA-256 `3d28a164bd567faf3b9a4a9271d452dae6c576b1d67ddadb360f3c08aee7fd5c`. Its clean .olean is present. **No substantive defect found.** Root owns the separate all-local dependency audit.

## Exact graph bound

The finite graph is a literal `SimpleGraph V` on a finite vertex type. `complement_edge_identity` is derived from the exact degree sums of G and its complement. The empty-vertex branch is treated separately before converting the natural predecessor `|V|-1` to a real subtraction, so no truncated-subtraction error enters the polynomial identity.

For nonempty V, the proof explicitly derives `indepNum >= 1` from a singleton independent set. The complement has no clique of size `indepNum+1`. Mathlib's proved Turan maximal graph theorem and its actual edge-count upper bound give `2*alpha*e(complement) <= (alpha-1)*|V|^2`; together with the complement identity this is exactly `|V|^2 <= alpha*(|V|+2e(G))`. The natural-to-real subtraction conversion is justified by alpha>=1. No independent-set size premise, probabilistic premise or new graph axiom is supplied.

`exists_independent` then obtains an actual maximum-size independent Finset using the finite attainment theorem, rather than concluding only a bound on a supremum. For nonempty V the denominator is proved positive. For empty V the numerator is zero and Lean's zero-division convention yields zero; the actual empty independent set exists, so the stated empty case is correct rather than an omitted exception.

## Ordered-count convention

`orderedCount` is exactly the cardinality of the finite set of ordered pairs with G.Adj. SimpleGraph adjacency is symmetric and irreflexive, so diagonal pairs are absent and every unordered edge contributes precisely two ordered pairs. `orderedCount_eq` is the proved Mathlib equality `orderedCount = 2*|edgeFinset|`. Therefore `exists_independent_ordered` has denominator `|V|+orderedCount`, with no missing or duplicated factor two. It is the right interface for the actual ordered Gaussian collision count after restricting to the selected vertex type and proving graph adjacency matches those collisions.

The module does not itself construct that Gaussian collision graph or relate it to a particular random count; those remain separate assembly obligations and are not hidden assumptions of this finite graph theorem.
