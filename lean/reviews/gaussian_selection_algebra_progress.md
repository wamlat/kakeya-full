# Scalar retained population for actual Gaussian collision selection

`GaussianSelectionAlgebra.lean` is frozen, clean-compiled and exact-source audited PASS. SHA256: `3c3a7328fea7ce04c314b8232afe62e85331cc82a13ce761017f6fb6f523b324`.

All five named source theorems, seven local theorem declarations and nine total local declarations were checked by the production all-declaration audit appended to an exact copy of the complete source. All axiom dependencies are standard; there are no custom axioms, sorry/admit/native_decide, warnings or errors. See `gaussian_selection_algebra_audit.json` and `GaussianSelectionAlgebra_SourceAudit.log`.

For any fixed C>0, define

    H(C) = 1/log(2) + 4*C,
    c(C) = 1/(4*H(C)) > 0.

`denominator_bound` proves that V<=M and E<=4*C*A*M*L imply V+E<=H(C)*A*L*M when M>=0, A>=1 and L>=log(2). The diagonal V term is absorbed using A*L/log(2)>=1; no scale-dependent positive margin is assumed.

`population_lower` combines M/2<=V<=M, E>=0, the same collision budget, C>0, A>=1 and L>=log(2), obtaining

    c(C)*M/(A*L) <= V^2/(V+E).

For M>0, the denominator is strictly positive, V^2>=M^2/4, and the explicit denominator bound yields the result by valid positive-denominator inequalities. For M=0 the assumptions force V=E=0; both real ratios are zero. The generic real statement explicitly requires E>=0: omitting this is false for arbitrary negative real E, and the actual collision cardinality automatically supplies it.

`cardinality_lower` is the direct natural-cardinality API for the collision graph. Its M,V,E are naturals, so nonnegativity is derived internally. Its hypotheses are M/2<=V, V<=M, E<=4*C*A*M*L, C>0, A>=1 and L>=log(2). It gives exactly the same ratio lower bound, including empty graphs. E is the ORDERED collision count, i.e. the quantity matching V+2e in the undirected graph convention.

The finite agent's actual GaussianCollisionSelection.select theorem proves V^2/(V+E)<=selected_card with exactly this whole-family ordered E. The parent's GaussianRealization supplies V>=M/2 and the displayed E budget for one actual matrix, with C=expectationCoefficient(20) and L=log(2/delta). Therefore this scalar module is directly composable with actual constructions; it does not assume a selected population or the desired M/(A*L) conclusion. It is intentionally a scalar lemma, not an independent graph or probabilistic existence theorem.

Commands in `audit_work/formalization` with pinned matching Lean/mathlib:

```sh
lake env lean -o .lake/build/lib/lean/GaussianSelectionAlgebra.olean GaussianSelectionAlgebra.lean
python3 ../audit_gaussian_selection_algebra.py
```

Related read-only reviews: `gaussian_realization_scalar_review.md` and `gaussian_collision_selection_scalar_review.md`. The parent owns integrated publication; this module stays outside the frozen registry until explicitly included there.
