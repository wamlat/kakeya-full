# Kakeya formalization — checkpoint 23

The frozen package contains **427 modules**, **3316 source theorem/lemma declarations**, and **8549 audited local declarations**. Its complete build, dependency audit and **131 exact checks pass**. The source coverage and its qualifications are recorded in [AUDIT.md](AUDIT.md) and the [completion audit](reviews/checkpoint23_completion_audit.md).

Start with [LebesgueMaximal.lean](LebesgueMaximal.lean) for the shading conclusions on arbitrary Lebesgue-measurable sets, including `six_first` at M6(33/8) and `six_first_step` for M6(4)→M6(33/8). It proves exact equivalence with the Borel-set statements in [MainMaximal.lean](MainMaximal.lean), preserving constants and original volumes. [MainOperator.lean](MainOperator.lean) proves the actual strong maximal-operator bounds for a.e.-measurable functions. These main chains use only standard Lean foundations.

This checkpoint additionally completes the original Gaussian projection route, the source whole-sphere sampling net and probability greater than3/4, the same-outcome geometric realization, and both prescribed appendix bush iterations. Individual-length cumulative, actual-volume and operator conventions are included. The module files form one project; a main entry-point file needs its imported dependencies.

Exactly three user-authorized published inputs are registered as custom axioms. Their statements, source translations and every dependent declaration are documented in [AXIOMS.md](AXIOMS.md). No novel manuscript conclusion is axiomatized.

## Reproduce

Requires Lean4.33.1 and Mathlib `0df444a360eaa60ab8c11dca51a86af692955474`.

```sh
python3 verify.py --mathlib-project /absolute/path/to/matching/mathlib/project
```

The verifier copies this frozen source into a separate scratch project, builds every registered module, then audits every local declaration, including definitions, proof-bearing data and generated declarations. It rejects admissions, unsafe proofs, native_decide and unregistered axioms. The supplied dependency project's sources remain untouched. Options include `--scratch`, `--log-dir`, `--workers` and `--lake`.

For a fresh dependency setup, run `lake update`, `lake exe cache get`, then `python3 verify.py`. The recorded run reused matching installed dependencies and a filesystem clone of the verified unchanged 406-module local build cache. Lake validated the enlarged snapshot, and the declaration audit recompiled every exact module source; no cached per-module audit was substituted. See [cache provenance](reviews/checkpoint23_build_cache_reuse.json). A cold-cache build and fresh dependency downloading were not separately tested. `--reject-external-axioms` deliberately rejects the package's registered published assumptions. The portable verifier regression suite has12 passing cases against this exact verifier hash.

## Evidence

- [verification/summary.json](verification/summary.json): versions, all exact source hashes, every local logical dependency and compiler results.
- [verification/lake-build.log](verification/lake-build.log): complete integrated build.
- [MODULES.md](MODULES.md): the full source inventory and declaration counts.
- [Completion audit](reviews/checkpoint23_completion_audit.md): requirements mapped to actual evidence, with qualifications.
- [source_manifest.json](source_manifest.json): supplied documents and their unchanged hashes.
- [output_manifest.json](output_manifest.json): hashes of all other delivered files.

Historical reviews describe their original snapshots. The verifier's summary now describes its actual logical-dependency scope; matching formal statements to the manuscript is documented separately in the completion audit. The checking logic and embedded Lean audit are unchanged, and12 regression cases passed against the delivered verifier hash.
