# Uniform cardinality budget for the actual whole-sphere net

`SphereNetBudget.lean` is frozen, clean-compiled and exact-source audited PASS. SHA256: `cd2eea7bd08900bab48039b927d4da90e1fda76998b6c1a4e02946c9959cc465`.

All five named theorems and all five local declarations passed the production all-declaration audit on the exact complete source. Dependencies use only standard axioms; no custom axioms, sorry/admit/native_decide, warnings or errors occur. See `sphere_net_budget_audit.json` and `SphereNetBudget_SourceAudit.log`.

The input geometric object is the actual ProjectiveSphereNet.Net k theta, whose entire-sphere construction and packing bound are proved in the preceding module. No separate net cardinality or coverage estimate is assumed here. `theta_pos` derives theta>0 directly from the net's strict coverage of the genuine unit axis vector; the dimension k=0 still has a nonempty one-dimensional unit sphere, so this argument includes it.

`polylog_count` combines the actual net packing bound with 1/theta<=B*log(2N)^q, obtaining the exact expression

    card(net.points) <= packingConstant(k)*B^k*log(2N)^(q*k).

The natural power k on the inverse radius is converted to the real log exponent q*k using the positive-log real-power identity. N>=1 ensures the logarithm is nonnegative. This intermediate identity does not require q>0 or division by k; k=0 and q=0 are included exactly.

`exists_threshold` fixes k, B>0 and q>=0 before obtaining a threshold N0>=1. It applies LogLoss.log_power_uniform_bound with exponent q*k and scale loss ONE, giving log(2N)^(q*k)<=C*N for all N>=1. The remaining fixed coefficient is H=packingConstant(k)*B^k*C. Taking N0=max(1,H) yields H*N<=N^2. Therefore, for EVERY N>=N0, theta, and actual net satisfying the inverse-radius budget, its actual point cardinality is <=N^2. Neither theta, the particular net nor N affects the chosen threshold. There is no assumed desired N^2 count or scale-dependent coefficient hidden in the conclusion.

`product_count` is a statement about the actual finite product S x net.points. From card(S)<=P*N^D and the derived net count, it proves card(product)<=P*N^(D+2). The exact card_product identity and positive-base real-power product are used. `exists_product_threshold` combines this with the same uniform threshold; D and P occur after it because the spatial prefactor is PRESERVED, not absorbed. Taking P=1 gives literally N^(D+2). If the actual spatial count has a fixed prefactor greater than one, that prefactor remains explicit in the output.

This closes the numerical whole-sphere-net cardinality step used in source (6.19). The literal theta choice and its inverse-log budget must still be instantiated from the source sampling parameters; the preceding geometric net construction and the later actual cap-test/probability union bound are separate modules. The theorem neither assumes those probability conclusions nor claims to establish them from a cardinality count alone.

Commands in `audit_work/formalization` with pinned matching Lean/mathlib:

```sh
lake env lean -o .lake/build/lib/lean/SphereNetBudget.olean SphereNetBudget.lean
python3 ../audit_sphere_net_budget.py
```

Independent read-only review of the preceding entire-sphere net is saved in `projective_sphere_net_scalar_review.md`. This new source remains outside the earlier frozen registry until the parent's next integrated checkpoint.
