# AngularDecomposition: actual pointwise finite broad decomposition

`audit_work/formalization/AngularDecomposition.lean` contains 14 theorem declarations, cleanly compiled with Lean 4.33.1 and Mathlib commit 0df444a360eaa60ab8c11dca51a86af692955474. Namespace `KakeyaFormal.AngularDecomposition`.

## Main completed theorem

`common_scale_broad_decomposition` applies to any nonempty finite subset V of indices of an actual unit-direction TubeFamily, for every 0<delta≤1 and beta≥0. It constructs a natural J, an actual common scale tau=radius(J,j) and a finite collection of pairwise disjoint subsets W of V, with:

- `J ≤ log(1/delta)/log2` and `delta ≤ tau ≤ 1`;
- total retained cardinality at least `|V|/[2*(J+1)]`;
- every W is nonempty and lies in a projective cap of radius2tau centered at an actual original direction;
- every W has cardinality at least `tau^beta*|V|/2`;
- for every actual projective cap center and every real radius r≥delta, `|W intersect cap(center,r)| ≤ 4^beta*(r/tau)^beta*|W|`;
- the number of selected pieces is at most `2*tau^(-beta)`.

For the manuscript's 0<beta≤1, the broadness error4^beta is at most4. All pieces are original tube-index sets, not abstract points standing for them. The theorem does not assume original direction separation or distinct directions. Its cap centers in the broadness conclusion need not be unit vectors. The conclusion handles every real r≥delta, not only dyadic test scales.

## Proof content

1. Candidate caps are a finite set: centers range over existing remaining directions and radii are twice the finitely many dyadic scales between the chosen bottom and1. The score is actual population divided by scale^beta. Mathlib's finite maximum theorem constructs a maximizer.
2. A top candidate of radius2 contains all unit directions, since actual projective chord distance is at most2. Thus the maximizing cap W contains at least tau^beta times the remaining population.
3. For an arbitrary cap intersecting W, choose an actual incident index as a new center. The projective triangle inequality puts the queried directions into a radius2r cap about that index. Round r upward to one of the finite candidate scales. The actual real bottom scale introduces at most a factor4, yielding the precise broadness error4^beta. When r>1, the top radius2 cap supplies the bound directly.
4. The finite saturation theorem constructs a maximal total-population disjoint collection of good pieces among an explicit finite powerset of candidates. If the uncovered remainder were larger than half, step1 would supply another nonempty good piece inside it, contradicting maximality. This proves actual disjoint selection and half-population retention, rather than assuming a greedy output or a desired rounding property.
5. A weighted finite pigeonhole step chooses a radius class by total retained population, not by merely counting pieces. It costs exactly J+1. Pairwise disjointness bounds total population by |V|, while the individual tau^beta|V|/2 lower bound gives the piece count2tau^(-beta).

This is a finite variant of the pointwise vector argument in manuscript Section3.2. It does not need deletion of a100-fold enlarged cap: saturation by disjoint retained subsets already provides the required pointwise population and piece-count conclusions, and the manuscript explicitly says geometric disjointness of enlarged caps is unnecessary. The proof uses containing caps of radius2tau and broadness factor4^beta, which are permitted fixed constants in that argument. It also avoids leaving the existence of a maximum over continuous cap centers/radii unproved.

## Broadness inheritance

The module also defines actual `Broad` projective cap counts and proves `broad_biUnion` for pairwise disjoint actual index sets at a common scale. The proportional-subset theorem `broad_proportional_subset` takes small⊆large and |large|≤D|small| and changes broadness error K to K*D. These are the precise finite inheritance rules needed after later cap and spatial assignment; they do not assume that the assignments preserve broadness automatically.

## What is not yet claimed

This module proves the pointwise finite direction-set decomposition only. It does not yet give the entire Lemma3.2 about shadings. In particular it does not construct the bounded-overlap global angular cap cover, assign each tube to a globally chosen cap, perform the proportional pointwise deletions after assignment, build the transverse spatial lattice covering tubes, or assemble the three incidence-mass pigeonhole losses into L^(-3). Measurable dependence of the whole global construction is not asserted. The finite output is a deterministic-choice-compatible mathematical existence result, and future cellwise use can select it for each finite incidence pattern, but that global selection step needs its own theorem.

## Verification

From `audit_work/formalization`:

```
/Users/ssoh/.elan/bin/lake env lean -o .lake/build/lib/lean/AngularDecomposition.olean AngularDecomposition.lean
/Users/ssoh/.elan/bin/lake env lean ../angular_decomposition_axioms.lean > ../angular_decomposition_axioms.log
```

The audit source is the exact module source plus `#print axioms` for all14 declarations. All are checked to use only `propext`, `Classical.choice`, and `Quot.sound`; no sorry, admit, native_decide or new axiom is permitted. The auxiliary exploratory CheckAngular.lean stays outside the development module directory and is not part of this verified module.
