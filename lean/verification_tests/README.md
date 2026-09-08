# Portable verifier regression tests

Run these 12 synthetic fixtures to check the package verifier's external-axiom boundary. The suite builds only small, real Lean fixture libraries, using the same Lean toolchain and pinned Mathlib dependency. It does **not** rebuild the full Kakeya package or rerun its mathematical arithmetic suite.

From the delivered package directory:

```sh
python3 verification_tests/run_regression.py \
  --mathlib-project /path/to/matching/dependency/project \
  --lake /path/to/lake \
  --work-dir /path/to/scratch
```

`--package` defaults to the parent of this test directory. Set it explicitly when testing a different package:

```sh
python3 /path/to/verification_tests/run_regression.py \
  --package /path/to/package \
  --mathlib-project /path/to/matching/dependency/project \
  --lake /path/to/lake \
  --work-dir /path/to/scratch \
  --result-json /path/to/results.json
```

The dependency project must already have its `.lake/packages` directory and matching `lake-manifest.json`; the suite checks the Mathlib revision against the package pin. If dependencies are installed in the package itself, omit `--mathlib-project`. Lake is discovered from `PATH`, with the usual home-directory Elan shim as a fallback. `--workers` defaults to 3. All options are listed by `--help`.

Every run creates a fresh subdirectory under `--work-dir`, preserving fixture sources, the tested verifier snapshot, full compiler/audit logs, commands, and summaries. The default work directory is `verification-test-work` under the current working directory. The portable summary defaults to `results.json` beside this script; use `--result-json` if that folder is read-only. A successful run exits zero and records `PASS` for all 12 cases, plus verifier, harness, and fixture hashes.

The cases cover ordinary and registered proofs, an unregistered local axiom, an imported unregistered dependency, an incorrect registry hash, both strict-mode outcomes, `sorry`, `native_decide`, Type-valued proof definitions, opaque proof records, and a registered proof definition. Negative cases must fail for the intended reason; a compiler failure alone does not count as a successful rejection test. Registered proof definitions must appear in the declaration dependency inventory without being counted as dependent theorems.

The registry fixtures use a synthetic axiom of `True` and an intentionally invalid example URL. Their `exact_checks.py` is a zero-check stub solely for verifier control flow. These fixtures do not import a mathematical result, and their successful tests are separate from the package's main proof verification. No production verifier, registry, module, or dependency source is modified.

The adjacent [results.json](results.json) records the packaging-time run. The [independent verifier review](../reviews/external_axiom_verifier_review.md) explains the discovered and corrected proof-definition coverage gap.
