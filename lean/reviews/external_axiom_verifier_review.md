# Independent external-axiom verifier tests

6 September 2026. Scope: `audit_work/formalization/verify.py`. I edited only scratch fixtures, test scripts, and this report. Root applied the production correction described below.

**Result: one coverage hole was reproduced, corrected, and regression-tested.** The current production verifier passed all 12 requested and supplementary cases. All eight negative cases were rejected for their intended reason; all four positive cases passed.

## Method and reproducibility

Each case receives a byte-for-byte copy of the verifier, a minimal real Lean library, the matching pinned Mathlib manifest/toolchain, and an isolated scratch build directory. The tests call the verifier normally, including `lake build` and its generated Lean `AUDIT` command. They do not fabricate audit output or substitute a fake compiler. The dependency source directories and production modules are untouched. The fixture's `exact_checks.py` returns a trivial zero-check JSON solely to let the axiom-verification tests reach their normal completion path; this does not retest the manuscript's arithmetic suite.

Toolchain: Lean 4.33.1, Mathlib commit `0df444a360eaa60ab8c11dca51a86af692955474`.

Initial verifier snapshot SHA-256:

`92fd2f83c88e125bd617a7fdd5e0454ea0e874cb463b916a28f999a79ec3ba6a`

Corrected production verifier SHA-256, independently rechecked after the regression:

`cdea72e87c59d8e7b92a67268a42698f7e374d1cbce68560d022302eb2649ab6`

Reproduce the final suite from the delivered package directory:

```sh
python3 verification_tests/run_regression.py \
  --mathlib-project /path/to/matching/dependency/project \
  --lake /path/to/lake \
  --work-dir /path/to/scratch
```

The delivered [portable runner](../verification_tests/run_regression.py), [README](../verification_tests/README.md), and [packaging-time results](../verification_tests/results.json) are independent of the development folder name and contain no hardcoded user paths. They support explicit package, dependency-project, Lake, work-directory, and result-file options. Each run preserves its complete fixture sources, verifier snapshots, invocation logs, actual Lean logs, and JSON summaries under a new scratch directory. The portable runner was tested against the production verifier, including from a relocated package layout with default package discovery and a relative Lake path.

Historical development evidence remains in `audit_work/external_axiom_verifier_tests/`, with `production_results.json` and `production_regression_assertions.json`. The earlier development scripts and the portable runner passed Python syntax checks. The portable suite supersedes the development-specific reproduction commands.

## Reproduced hole and correction

The initial verifier collected dependencies only when `ConstantInfo.isTheorem` was true. It therefore accepted this Type-valued proof record under its standard-foundations mode:

```lean
import Lean
set_option linter.deprecated false
structure Certificate : Type where
  proof : True
def proofCertificate : Certificate := ⟨Lean.trustCompiler⟩
theorem unrelated : True := True.intro
```

This source has no compiler warning. The separate actual Lean output was:

```text
'proofCertificate' depends on axioms: [Lean.trustCompiler]
```

The old audit emitted only unrelated/generated theorem entries without that dependency, and the complete old verifier returned `PASS`. This is stronger evidence than merely observing that definitions were omitted by inspection. An initial Prop-valued `def` probe instead triggered Lean's `linter.defProp`; the Type-valued record was needed to demonstrate that warning rejection did not close the coverage gap.

The tested correction preserves the theorem inventory and additionally runs `Lean.collectAxioms` on every other local constant, emitting `AUDIT_DECLARATION`. The Python allowlist checks the union of dependencies from both inventories. The production summary now separately records all declaration dependencies and external-dependent declarations, while keeping theorem counts distinct. Lean's collector handles definitions and opaque values, including their proof fields; the opaque case was independently exercised.

The corrected verifier rejects the exact formerly accepted record with `unexpected axioms {'Lean.trustCompiler'}`. A corresponding opaque record is rejected for the same reason. The correction was first tested in a fixture copy, then tested again after root applied it to production.

## Final production regression

| Fixture | Expected and observed result |
|---|---|
| Standard theorem, no external registry entries | PASS; standard-foundations mode |
| Registered synthetic axiom and dependent theorem | PASS; exact external dependency recorded |
| Unregistered local axiom and dependent theorem | Reject; declared/expected axiom mismatch |
| Theorem using imported unregistered `Lean.trustCompiler` | Reject; unexpected dependency |
| Registry module hash mismatch | Reject before compilation; reviewed hash mismatch |
| Registered external axiom with `--reject-external-axioms` | Reject before compilation; strict mode |
| Standard theorem with `--reject-external-axioms` | PASS |
| `sorry` proof | Reject; forbidden proof construct |
| `native_decide` proof | Reject; forbidden proof construct |
| Type-valued proof definition using unregistered axiom | Reject; unexpected dependency |
| Opaque Type-valued proof record using unregistered axiom | Reject; unexpected dependency |
| Type-valued proof definition using registered axiom | PASS; definition dependency recorded separately |

In the last case the summary correctly records `Fixture.proofCertificate → Fixture.published`, while the external-dependent theorem count remains zero. The all-declaration external count includes the registered axiom itself and the proof definition, as expected from that inventory's scope.

## Actual production axiom module

I also compiled the actual `ExternalAxioms.lean` source with the original and expanded audit commands, resolving its genuine imports against the already-built development project. Both compiled without diagnostics. The expanded audit reported the same three authorized names, the three standard foundations only, 13 environment theorem entries, and five other declaration entries in that generated audit file. These environment entries are not a count of handwritten theorem statements.

The exact artifacts are `ActualExternalAxioms_AxiomAudit.lean`, `actual_external_audit.log`, `ActualExternalDeclarations_AxiomAudit.lean`, and `actual_external_declarations_audit.log` under the fixture directory. No unregistered axiom appeared. Root's full frozen-package build/audit remains the separate package-wide verification; this test did not run a duplicate 199-module build.

No further defect was found in the exercised external-axiom acceptance/rejection paths. The registry's source-statement fidelity remains a human review obligation, covered separately by `external_axiom_statement_review.md`; a hash check cannot prove that an imported theorem was stated faithfully.
