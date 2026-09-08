# Explicit source-consequence wrappers

Two new modules are frozen and clean-built, with exact-source audits passing all seven theorems under only `propext`, `Classical.choice`, and `Quot.sound`. No frozen module or registry was modified.

## Lemma2.1, equation(2.2)

`ProjectionConclusion.lean`, SHA256 `db6e3a985bab44768929d9863c581a7ec8755713b9aea753a0fe7cee67cc62bb`.

`source_cumulative` gives the exact δ^(1/2+eps)*s^(7/2+eps) formula for actual ambient-seven cap-four cumulative configurations. `source_count` unfolds the statement to the original TubeFamily, arbitrary real N≥1, A≥1, s≥0, original finite shadings and total incidence hypothesis s*N*M≤sum_i#shade_i. Its conclusion is exactly c*A^(-1)*N^(-1/2-eps)*s^(7/2+eps)*M≤#actualunion. The constant is fixed by geometry and eps before all N,A,s,M,F. Empty shadings and arbitrarily small s are included, without a per-tube density premise or log(1/s).

The conclusion is proved through the actual full-range fractional seed and cumulative conversion. This does not claim the separate Gaussian projection/independent-set construction has been formalized. The fixed grid/width/separation/bounded-position normalization remains the same visible convention as the existing discrete estimate.

## AppendixA.2 andA.3, all n≥5

`AppendixEndpoints.lean`, SHA256 `287a5eef6ceb74dce60587b2d13ce1d4876841a9e8f24a73dc0a7bc958c2e75e`.

`bush_discrete` and `weakened_bush_discrete` prove the actual diagonal estimates at (4n+4)/7 and (4n+3)/7. `bush_maximal` and `weakened_bush_maximal` give the literal cap-free, arbitrary-position measurable maximal-shading predicates for every integer n≥5. For n≥6 the stronger main endpoint dominates (4n+4)/7; for n=5 the standard proved cap-four fractional seed gives7/2, which exceeds both24/7 and23/7. Both set and density powers are weakened using the valid integer-shading theorem, followed by the actual measurable/spatial adapters. No naive decrease of only the measurable density exponent is used.

These named conclusions do not construct the optional bush iterations as an alternative proof route. They also do not assert the table's fractional diagonal fixed point25/7 in dimension five or any larger dimension-five main profile.

## Inventory effect

The earlier report-only coverage of(2.2) and both AppendixA endpoints now has explicit public Lean theorem names. The Gaussian route and bush iteration route remain distinguishable alternative constructions, not missing consequences. Checkpoint19's separate Proposition8.1 range0<C<1 still lacks a dedicated named wrapper if its literal formulation is desired; its conclusion follows from density weakening to1 and max(D,1)=D for D>1, within the existing actual two-ends predicate. The manuscript's absolute-cap-only hypothesis is weaker than that predicate and should not be conflated with the already formalized stronger-input formulation.

Validation: both production `.olean` builds are clean, zero diagnostics. Complete exact source was independently compiled with appended `#print axioms` for every named theorem; metadata/source prefixes/final SHA were checked. Adjacent `ProjectionConclusion_full_source_audit` and `AppendixEndpoints_full_source_audit` lean/json/log files record the evidence.
