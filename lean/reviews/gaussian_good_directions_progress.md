# Actual Gaussian good-direction event before source (2.3)

`GaussianGoodDirections.lean` is frozen, compiled with zero diagnostics, and exact-source audited PASS. SHA256: `c76c9a6dabf0f62d3265c609ca542c39df747f2ed3085d098aa5cc162dfd6da9`.

The audit checked all 16 named source theorems, 29 local theorem declarations, and 34 total local declarations. Every axiom dependency is standard (`propext`, `Classical.choice`, `Quot.sound`); there are no custom axioms, forbidden proof shortcuts, warnings or errors. Details are in `gaussian_good_directions_audit.json`; exact whole-source audit transcript: `GaussianGoodDirections_SourceAudit.log`.

This closes the actual positive-probability assertion at combined.txt lines230–234, immediately before (2.3). The sample space and law are the original standard Gaussian five-by-seven matrix. The theorem chooses fixed K=20 and c=1/4 and uses the same actual matrix for every direction. Every input is an arbitrary finite indexed family of unit vectors in R^7; distinctness, cap bounds, angular separation and independence between different projected directions are not assumed.

The generic `small_event_bound` derives P(||Pv||<c)<=(2c)^rows from the previously proved actual unit-vector marginal law and the standard Gaussian small-ball bound. The strict bad event is contained in the corresponding closed ball, so no boundary convention is silently changed. The actual `badIndices` is the finite filter on the original indices. `badCount_sum` identifies its real cardinality exactly with the finite sum of measurable indicators, and `expected_badCount` integrates this actual sum to obtain E badCount<=M*(2c)^rows. This step needs only linearity of finite expectation, even when input directions coincide.

`half_bad_probability` applies real Markov with threshold M/2 and M>0. In five dimensions at c=1/4 this gives P(badCount>=M/2)<=1/16. The original indices satisfying c<=||Pv|| are `goodIndices`, with equality retained; their count plus badCount equals M exactly. The M=0 case is handled separately in `countFailure`, avoiding division by zero or a false half-count failure bound.

The parent's actual norm-tail theorem gives P(||P||>=20)<=7/80. The union of this event and countFailure has probability at most 3/20. Its complement is contained in the literal `goodEvent`, which requires ||P||<=20 and at least M/2 actual good indices. Consequently:

```lean
GaussianGoodDirections.good_probability v hv :
  (17/20:Real) <= (GaussianMatrix.law 5 7).real (goodEvent v)
```

`good_probability_three_quarters` supplies the simpler 3/4 lower bound. `exists_good_matrix` constructs an actual matrix outcome with the actual good-index finite set, its at-least-half cardinality, the operator norm bound, and the pointwise image lower bound for every retained original index. No event probability, norm moment, good-count, or independence conclusion is supplied as a premise.

The new module intentionally stops at this positive-probability event. Summing pairwise angular collisions, imposing their Markov cutoff simultaneously, extracting an independent set, and transferring actual projected grid/shading geometry are subsequent parts of the source projection route; this module does not claim those conclusions. The orthogonal-pair collision law is proved separately in the existing Gaussian modules.

Commands, run in `audit_work/formalization` with the pinned Lean/mathlib project:

```sh
lake env lean -o .lake/build/lib/lean/GaussianGoodDirections.olean GaussianGoodDirections.lean
python3 ../audit_gaussian_good_directions.py
```

The audit appends the production all-declaration audit to an exact copy of the complete source, compiles it, checks every reported axiom, and checks coverage of every named source theorem. This is an individual checkpoint, not an assertion of integrated publication. Independent read-only review of the actual operator and moment inputs is saved in `gaussian_operator_scalar_review.md`.
