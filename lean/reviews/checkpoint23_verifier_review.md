# Verifier metadata correction and regression evidence

The checkpoint23 verifier differs from the checkpoint22 verifier only in the human-readable `summary.scope` sentence. Exact whole-file comparison after substituting that one string succeeds. No Python checking logic, embedded Lean environment audit, accepted foundations, registry handling, source coverage rule, compiler command, or diagnostic rejection rule changed.

- Previous verifier SHA-256: `cdea72e87c59d8e7b92a67268a42698f7e374d1cbce68560d022302eb2649ab6`.
- Updated verifier SHA-256: `419584e57059334f50092d3fe72782c71b5f50d7c19198a44cd4b3cae3e42799`.
- Regression harness SHA-256: `38755e6bec47e6033f0aca2f8e5e1ab70ef9268f63260f04216e8f632c51b9a1`.

The old sentence asserted unfinished main analytic/geometric dependencies irrespective of the module contents. The new sentence describes the actual logical-dependency audit and explicitly leaves manuscript correspondence to the separate source audit. It makes no automatic claim that every manuscript result is covered.

The portable regression suite passed all12 cases against the new verifier hash: four intended acceptances and eight intended rejections. It verifies standard proofs, exact registered assumptions and proof-bearing definitions, strict standard-only mode, rejection of an incorrect registry hash, unregistered axioms and compiler-trust dependencies, admissions, and native-decide proofs. The verifier file remained unchanged throughout the run. These are small real Lean fixtures; they supplement rather than replace the final full mathematical package build and source audit. Exact case records are in `checkpoint23_regression_results.json`; current-run fixtures and logs are packaged with the final regression results.

The completed checkpoint22 integrated run used its original verifier throughout and remains unchanged. All418 sources in the initial checkpoint23 freeze were also checked lexically for kernel-bypass names; the only non-registry hits were prose comments, and no bypass implementation was found. This bounded lexical check is additional evidence, not a substitute for checking every local declaration's actual logical dependencies.
