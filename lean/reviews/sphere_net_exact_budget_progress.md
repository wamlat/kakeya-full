# Exact sphere-net test budget, including fixed prefactors

`formalization/SphereNetExactBudget.lean` is frozen at SHA-256
`3962cc9ebd618e80efd01e0cca1a553d299550a41f530bb3418932e21220df52`.
Clean compilation has zero diagnostics and a matching `.olean`. The exact
whole-source production audit passed all 3 named theorems, 3 local theorem
declarations, and 3 total local declarations. Dependencies are restricted to
`propext`, `Classical.choice`, and `Quot.sound`; there are no custom axioms,
`sorry`, `admit`, or `native_decide`.

The three proved APIs in `KakeyaFormal.SphereNetExactBudget` are:

- `linear_count_budget`: fixed k, B>0 and q>=0 determine H>0 before all N>=1,
  theta, and actual `ProjectiveSphereNet.Net k theta`. The inverse-radius
  bound 1/theta <= B*log(2N)^q implies the actual net cardinality <= H*N.
- `exists_product_threshold`: additionally fix P>0. One threshold N0>=1
  gives `card(S × net.points) <= N^(D+2)` for every actual finite S satisfying
  card(S) <= P*N^D. The arbitrary real D occurs after the threshold.
- `exists_augmented_threshold`: under the same ordering and hypotheses,
  `card(S)*(1+card(net.points)) <= N^(D+2)`. This is the literal event count
  including both one marked-cell lower-tail test and all cap upper-tail
  tests at every cell, as required in source (6.19).

The actual net count follows from its constructed spherical packing bound
and `log_power_uniform_bound` at exponent q*k and power allowance 1. The
thresholds are max(1,P*H) and max(1,P*(1+H)), respectively. They absorb the
fixed spatial prefactor without increasing the exponent D+2. No net-count
premise or assumed covering is used. k=0, q=0, empty S, and arbitrary real D
are included; N is always positive through N>=1.

This is a numerical test-budget interface. Deriving the inverse-radius
budget from the source theta choice, deriving the actual spatial support
bound, and composing the probability tails remain in their respective
geometric/probability modules. It does not assert sampling probability by
itself. The earlier `SphereNetBudget.lean` remains unchanged and frozen.

Reproduction from `audit_work/formalization`:

```
/Users/ssoh/.elan/bin/lake env lean -o .lake/build/lib/lean/SphereNetExactBudget.olean SphereNetExactBudget.lean
python3 ../audit_sphere_net_exact_budget.py
```

Evidence: `sphere_net_exact_budget_audit.json`,
`SphereNetExactBudget_SourceAudit.lean`, and
`SphereNetExactBudget_SourceAudit.log`. Toolchain/dependencies are the same
pinned Lean 4.33.1 and mathlib revision
`0df444a360eaa60ab8c11dca51a86af692955474` as the development package.
This new module is outside the frozen checkpoint21 package; no existing
source, registry, lakefile, verifier, or published output was edited.
