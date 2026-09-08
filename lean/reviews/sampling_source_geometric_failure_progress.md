# Actual source density and full-ball failure probability

`formalization/SamplingSourceGeometricFailure.lean` is clean compiled with
zero diagnostics and its production `.olean` is available. Frozen SHA-256:
`e3ce1d27d2e010fcdf44aedb56576b0ab9bee0e481a1088570f1a08c86ae4627`.
The exact-source audit passed both named theorems, both local theorem
declarations, and both total local declarations. Only `propext`,
`Classical.choice`, and `Quot.sound` occur; there are no custom axioms or
proof placeholders.

`SamplingSourceGeometricFailure.source_geometric_failure` fixes ambient
dimension k+1, width, position bound R, upper axis length L, separation
multiple sep>0, physical lower-density constant c0>0, and exponents
0<s<1 and 0<=alpha<1-s. It chooses one positive delta0<=1 before the actual
family, original full/marked measurable sets, individual lengths, scale,
density, upper-density constant, marked fraction, B, K, and beta.

For actual `SamplingLengthInput.Input`, original sep*delta separation,
delta<=delta0, and lambda>=delta^s, it constructs the actual finite dyadic
ball-test depth J. It proves the usual bottom-radius and depth inequalities
and a strict probability bound below 1/8 for the union of all full-tube
density failures and all full-ball upper failures. The probability is
literally computed under `SphereNetSourceFailure.rawLaw h`.

The full density failure event is the original lower threshold mu/2 or
upper threshold 2mu. This theorem does **not** assert the narrower
[2mu/3,4mu/3] interval of some previous sampling constructions. Its complement
has the source density band, and root's joint-event module handles the final
good-outcome record.

All needed inputs to the generic probability theorem are derived here:

- Actual original bounded carriers give finite old-cell support and actual
  ball-test cardinality at the constructed J.
- Original sep*delta separation gives the actual tube count. The cutoff
  additionally enforces delta<=1/sep. The combined number of tube-by-ball
  tests is bounded by a fixed constant times N^(2(k+1)), with its logarithmic
  depth explicitly absorbed.
- Original physical lower mass gives fullMean >= c0*lambda*N and hence
  c0*N^(1-s). The original full two-ends condition gives the actual tested
  ball-mean bound, and its cutoff is at least
  ballCoefficient(k)*c0*N^(1-s-alpha).
- Both powers are strictly positive by the fixed exponent hypotheses.
  The already proved stretched-exponential tails therefore give the fixed
  small-scale threshold. The constant B is only required to be >=1 and can
  vary after this threshold; no logarithmic B budget is needed here.

`law_eq_rawLaw` proves by definitional equality that the geometric-event law
is the same raw law as the angular-event module. Full/marked cell weights,
support, original axes, and tube indices are unchanged. No expected-count,
test-count, sampling-outcome, probability, or normalized-row oracle appears
in the public hypothesis. As in the original Input, the full population is
positive and the physical density is at most one.

Source coverage: the separate density and full-ball probability estimates
in (6.14)–(6.16), throughout the fixed positive-gap parameter range and for
original bounded variable-length axes. Combining this <1/8 bound with the
same-law angular <1/8 bound, yielding probability >3/4 and actual output
geometry, belongs to the root/geometry companion modules.

Reproduction from `audit_work/formalization`:

```
/Users/ssoh/.elan/bin/lake env lean -o .lake/build/lib/lean/SamplingSourceGeometricFailure.olean SamplingSourceGeometricFailure.lean
python3 ../audit_sampling_source_geometric_failure.py
```

Audit evidence: `sampling_source_geometric_failure_audit.json`,
`SamplingSourceGeometricFailure_SourceAudit.lean`, and
`SamplingSourceGeometricFailure_SourceAudit.log`. The audit uses the production
all-local-declaration collector on the full exact source, with standard-only
dependencies, and rejects diagnostics or proof placeholders. This new file
remains outside the frozen checkpoint21 package. No existing source,
registry, verifier, lakefile, or published output was changed.
