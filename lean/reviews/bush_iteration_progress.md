# Appendix A actual bush iteration route

The prescribed finite-stage route in Appendix A.2 and A.3 is now proved on actual configurations. This extends proof-route coverage; the endpoint conclusions were already available by a stronger independent route in `AppendixEndpoints`.

## New sources

- `BushIteration.lean`: SHA-256 `8077245382f010bec470501c8085ffa9fc7f163b4805bc683f444a7587142e90`. Clean compilation with zero diagnostics and `.olean` available.
- `BushIterationConsequences.lean`: SHA-256 `198d1fcc8443790e431513e19aafd9cda013bf54608ed519e5e52f31ad274798`. Clean compilation with zero diagnostics and `.olean` available.

## Actual mathematical content

| Source location | New checked result |
|---|---|
| Appendix A.2, (A.2), combined text lines 1975–1994 | `bush_step` constructs the actual lifted bush estimate in ambient n+1 with cap exponent d and set/density powers (d+2)/2, applies the direct positive-p pivot, and removes two ends. Its only induction premise is the previous actual diagonal base estimate. |
| Appendix A.2, (A.3)–(A.4), lines 1994–2016 | `bush_stage` supplies every actual finite iterate from the actual original bush seed (n+1)/2. `bush_endpoint` uses finite-stage convergence with a stage selected before the configuration for each requested scale error, obtaining (4n+4)/7 for every integer n≥5. |
| Appendix A.3, lines 2019 onward | `weakened_bush_step` weakens only the lifted set power to (d+1)/2 while retaining density power (d+2)/2. `weakened_bush_stage` and `weakened_bush_endpoint` give its own complete finite iteration and limit (4n+3)/7. |
| Appendix A measurable/maximal-shading conclusions | `BushIterationConsequences` applies the actual measurable and arbitrary-position adapters to both finite-stage sequences and both limits. |

The generic `direct_pivot` has only the actual base/lift estimate premises and explicit valid scalar tests. The final stage/endpoint theorems discharge those analytic premises internally. None assumes a marked output, angular decomposition, lifted cumulative estimate, normalization, spatial bound, or desired endpoint. The lifted ambient dimension is literally n+1. The early cases with lifted exponent at most 3 are handled by `PositiveTwoEndsPivot`; the narrower recursive Corollary 8.2 is not invoked.

The full density exponent is checked as max(D,C)=D at every stage. A.3 uses a proved set-only monotonicity lemma on the actual original mesh, not a density-exponent substitution. The two actual endpoint passages use the existing exact `DiscreteEstimate.of_limit`, preserving constants before mesh, density, cap coefficient, tube count, and all geometric configurations.

These new proofs use the original bush construction as seed and lift. They do not appeal to a stronger pre-existing endpoint theorem. The consequence module imports `MainMaximal` only to invoke its generic actual diagonal-to-measurable adapter.

## Audit and scope

`BushIteration`: production exact-source all-local audit PASS; 12 theorem entries / 12 total declaration entries, including generated local proofs. Only `Classical.choice`, `Quot.sound`, and `propext` occur. Evidence: `BushIteration_operator_audit.json` and `.log`.

`BushIterationConsequences`: production exact-source all-local audit PASS; 8 theorem entries / 8 total declaration entries. Only the same three standard foundational axioms occur. Evidence: `BushIterationConsequences_operator_audit.json` and `.log`.

Both modules are new and outside the frozen381 snapshot; no frozen source, common registry, lakefile, or verifier was modified. The final measurable predicate is the literal maximal-shading estimate, not an operator-norm assertion. The separately proved operator adapters are outside this bounded Appendix route task.
