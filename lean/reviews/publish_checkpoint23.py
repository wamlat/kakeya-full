#!/usr/bin/env python3
"""Publish only the completely verified frozen checkpoint23, with byte checks."""
from pathlib import Path
from datetime import datetime, timezone
import hashlib
import json
import shutil
import zipfile

work = Path(__file__).resolve().parent.parent
audit = work / 'audit_work'
dev = audit / 'formalization'
snapshot = audit / 'checkpoint23_verify'
logs = audit / 'checkpoint23_verification'
out = work / 'outputs/kakeya_verification'
archive = work / 'outputs/kakeya_verification.zip'
stage = audit / 'checkpoint23_publication_stage'
staged_archive = audit / 'checkpoint23_publication_stage.zip'
digest = lambda p: hashlib.sha256(p.read_bytes()).hexdigest()
summary = json.loads((logs / 'summary.json').read_text())
frozen = json.loads((audit / 'checkpoint23_frozen_source_hashes.json').read_text())
old = json.loads((audit / 'checkpoint21_frozen_source_hashes.json').read_text())
freeze = json.loads((audit / 'checkpoint23_freeze.json').read_text())
module_count = freeze['module_count']
new_since21 = module_count - 381
assert summary['status'] == 'PASS'
assert len(summary['modules']) == len(frozen) == module_count
assert set(frozen) == {m['module'] for m in summary['modules']}
assert len(old) == 381 and all(frozen[n] == h for n, h in old.items())
old22 = json.loads((audit / 'checkpoint22_frozen_source_hashes.json').read_text())
assert len(old22) == 406 and all(frozen[n] == h for n, h in old22.items())
assert summary['exact_named_checks'] == 131
assert len(summary['external_axioms']) == 3
assert summary['theorems_using_external_axioms'] == 7
assert summary['declarations_using_external_axioms'] == 10
assert digest(snapshot / 'verify.py') == freeze['verifier_sha256']
for m in summary['modules']:
    name = m['module']
    assert m['compiler_exit_code'] == 0
    assert m['source_sha256'] == frozen[name]
    assert digest(snapshot / (name + '.lean')) == digest(dev / (name + '.lean')) == frozen[name]
    if name != 'ExternalAxioms':
        assert not m['theorems_using_external_axioms']
        assert not m['declarations_using_external_axioms']
        assert set(m['axioms']) <= {'propext', 'Classical.choice', 'Quot.sound'}

validation = {
    'status': 'PASS', 'module_count': module_count,
    'source_theorems': summary['theorem_count'],
    'audited_theorems': summary['audited_theorem_count'],
    'all_declarations': summary['audited_declaration_count'],
    'exact_checks': 131, 'all_frozen_hashes_match': True,
    'old381_unchanged': True, 'external_axioms': 3,
    'external_dependent_theorems': 7, 'external_dependent_declarations': 10,
    'all_non_external_standard_only': True, 'old406_unchanged': True
}
(audit / 'checkpoint23_verification_validation.json').write_text(json.dumps(validation, indent=2) + '\n')

required_reviews = [
    'checkpoint23_finite_completion_audit.md',
    'checkpoint23_geometry_completion_audit.md',
    'checkpoint23_analytic_completion_audit.md',
    'checkpoint23_completion_audit.md',
    'checkpoint23_verifier_review.md',
    'paper_coverage_after_checkpoint21_finite.md',
    'sampling_source_complete_progress.md',
    'sampling_source_route_finite_review.md',
    'gaussian_projection_complete_progress.md',
    'bush_iteration_progress.md'
]
for name in required_reviews:
    assert (audit / name).is_file(), name
coverage = json.loads((audit / 'checkpoint23_completion_evidence.json').read_text())
assert coverage['status'] == 'PASS'
assert coverage['scope'] == 'mathematical_source_coverage'
assert not coverage['remaining_source_requirements']
assert coverage['frozen_source_hashes_sha256'] == digest(audit / 'checkpoint23_frozen_source_hashes.json')
assert coverage['verifier_sha256'] == digest(snapshot / 'verify.py')
assert coverage['integrated_summary_sha256'] == digest(logs / 'summary.json')
for name, expected_hash in {**coverage['semantic_reviews'], **coverage['review_indexes']}.items():
    assert digest(audit / name) == expected_hash, name
assert coverage['requirements'] and all(r['status'] == 'proved' for r in coverage['requirements'])
assert not stage.exists(), 'Staging directory already exists; inspect it before proceeding.'
stage.mkdir()
shutil.copytree(out / 'reviews', stage / 'reviews')
shutil.copytree(out / 'verification_tests', stage / 'verification_tests')
shutil.copy2(audit / 'checkpoint23_regression_results.json', stage / 'verification_tests/results.json')
shutil.copytree(logs, stage / 'verification')
for name in ['lakefile.lean', 'lean-toolchain', 'lake-manifest.json', 'verify.py',
             'external_axioms.json', 'exact_checks.py'] + [n + '.lean' for n in frozen]:
    shutil.copy2(snapshot / name, stage / name)
shutil.copy2(out / 'source_manifest.json', stage / 'source_manifest.json')
source_manifest = json.loads((stage / 'source_manifest.json').read_text())
for source in source_manifest['sources']:
    assert digest(Path(source['path'])) == source['sha256'], source['path']

# Preserve review history and include the actual source/hash-specific additions.
new_review_prefixes = ('gaussian_', 'five_dimensional_', 'projective_sphere_net',
                      'sphere_net_', 'sampling_geometric_failure', 'sampling_joint_probability',
                      'sampling_source_', 'bush_lengths', 'bush_iteration', 'cumulative_lengths',
                      'cumulative_fixed_error', 'lebesgue_', 'completed_', 'logarithmic_',
                      'wide_logarithmic_', 'six_dimensional_logarithmic_', 'source_localization_')
review_names = set(required_reviews)
for path in audit.iterdir():
    if path.is_file() and path.suffix in {'.md', '.json', '.lean', '.log'} and path.name.startswith(new_review_prefixes):
        review_names.add(path.name)
review_names.update(freeze['independent_reviews'].values())
review_names.update(['checkpoint23_completion_evidence.json',
                    'checkpoint23_finite_completion_hashes.json',
                    'checkpoint23_geometry_completion_hashes.json',
                    'checkpoint23_analytic_completion_hashes.json',
                    'checkpoint22_verification_validation.json',
                    'checkpoint23_build_cache_reuse.json',
                    'checkpoint23_initial418_freeze.json',
                    'checkpoint23_initial418_source_hashes.json',
                    'checkpoint23_extension_reviews.json',
                    'checkpoint23_publication_finite_review.md',
                    'checkpoint23_analytic_signature_checks.lean',
                    'checkpoint23_analytic_signature_checks.log',
                    'checkpoint23_completion_wording_scalar_review.md',
                    'checkpoint23_review_index_validation.json',
                    'validate_checkpoint23_review_indexes.py',
                    'build_checkpoint23_completion.py',
                    'publish_checkpoint23.py'])
for name in sorted(review_names):
    shutil.copy2(audit / name, stage / 'reviews' / name)
for name in ['checkpoint23_freeze.json', 'checkpoint23_frozen_source_hashes.json',
             'checkpoint23_verification_validation.json']:
    shutil.copy2(audit / name, stage / 'reviews' / name)
for name in set(freeze['individual_audits'].values()):
    shutil.copy2(audit / name, stage / 'reviews' / name)

regression_run = json.loads((audit / 'checkpoint23_regression_results.json').read_text())['work_subdirectory']
regression_root = audit / 'checkpoint23_regression_work' / regression_run
for case in json.loads((audit / 'checkpoint23_regression_results.json').read_text())['cases']:
    case_dir = regression_root / case['log_subdirectory']
    target = stage / 'verification_tests' / 'latest_run' / case['log_subdirectory']
    target.mkdir(parents=True)
    for name in ['Fixture.lean', 'verify.py', 'external_axioms.json', 'command.json', 'invocation.log']:
        shutil.copy2(case_dir / name, target / name)
    if (case_dir / 'logs').exists():
        shutil.copytree(case_dir / 'logs', target / 'logs')

regression = json.loads((stage / 'verification_tests/results.json').read_text())
assert regression['status'] == 'PASS' and regression['case_count'] == 12
assert regression['verifier_sha256'] == digest(stage / 'verify.py')
assert regression['harness_sha256'] == digest(stage / 'verification_tests/run_regression.py')

theorems = summary['theorem_count']
local_theorems = summary['audited_theorem_count']
declarations = summary['audited_declaration_count']
(stage / 'README.md').write_text(f'''# Kakeya formalization — checkpoint 23

The frozen package contains **{module_count} modules**, **{theorems} source theorem/lemma declarations**, and **{declarations} audited local declarations**. Its complete build, dependency audit and **131 exact checks pass**. The source coverage and its qualifications are recorded in [AUDIT.md](AUDIT.md) and the [completion audit](reviews/checkpoint23_completion_audit.md).

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
''')

(stage / 'AUDIT.md').write_text(f'''# Kakeya manuscript — checkpoint 23

Verified at {summary['utc']}. All{module_count} frozen modules build; all{declarations} local declarations, including{local_theorems} theorem declarations, pass the logical-dependency audit. All131 exact checks pass. Counts measure the checked package, not a percentage of mathematical correctness.

The current source audit maps every numbered theorem, lemma, proposition and corollary to an actual Lean proof route under the documented fixed geometric conventions. The [completion audit](reviews/checkpoint23_completion_audit.md) records the requirement-by-requirement evidence. The separate [finite](reviews/checkpoint23_finite_completion_audit.md), [geometry](reviews/checkpoint23_geometry_completion_audit.md) and [analytic](reviews/checkpoint23_analytic_completion_audit.md) reviews examine the source statements against their actual formal signatures. These reviews are part of the same AI-assisted development process; they are not independent human expert endorsements.

## Main conclusions

[MainMaximal.lean](MainMaximal.lean) proves the arbitrary-position measurable-shading assertion at33/8 in dimension6, its implication from M6(4), the endpoint `3+(2−sqrt(2))*(n−4)` for every integer n>=6, the exact six/eight radical endpoints, and29/7 and37/7 corollaries. The explicit [MaximalShading.Estimate](MaximalShading.lean) quantifies the positive constant before the actual scale, density, positions, population and measurable shadings. Actual tube-volume sums appear in the bound. No cap, two-ends, marking, sampling, localization or unpublished analytic premise remains in those main statements.

Those original set predicates use Borel shadings. [LebesgueMaximal.lean](LebesgueMaximal.lean) extends all principal unit and variable-length statements to arbitrary completed-Lebesgue-measurable sets, with exact equivalence and the same constants. [LebesgueRealCap.lean](LebesgueRealCap.lean) does the same for actual count, physical-volume, real-cap and variable-length estimates. [LebesgueLocalization.lean](LebesgueLocalization.lean), [LebesgueAngularSpatial.lean](LebesgueAngularSpatial.lean), [LebesgueDensityPruning.lean](LebesgueDensityPruning.lean), [LebesgueSeedDensity.lean](LebesgueSeedDensity.lean) and [LebesgueHairbrush.lean](LebesgueHairbrush.lean) provide the intermediate original-set conclusions, including exact masks and pointwise broadness where the source requires it. [LebesgueSamplingSource.lean](LebesgueSamplingSource.lean) and [LebesgueSamplingGeometry.lean](LebesgueSamplingGeometry.lean) retain the exact original support, raw arrays, law and physical outcome. [CumulativeFixedError.lean](CumulativeFixedError.lean) proves the literal single-error, fixed-cap-coefficient, one-logarithm cumulative corollary. [LebesgueDensityTrimming.lean](LebesgueDensityTrimming.lean) constructs the exact prescribed-mass subsets of original completed-measurable shadings. [SourceLocalizationGeometry.lean](SourceLocalizationGeometry.lean) derives the joint dyadic-radius, retained-population and density certificate from the actual original midpoint geometry. [SixDimensionalLogarithmicLengths.lean](SixDimensionalLogarithmicLengths.lean) proves first-step Lemma 6 for original logarithmic two-ends constants, arbitrary fixed density multiples and bounded individual lengths, with one constant before all original configurations.

[MainOperator.lean](MainOperator.lean) supplies the actual strong operator norm conclusions through [OperatorNorm.Estimate](OperatorNorm.lean): Mathlib eLpNorm on the original-position supremum of tube averages, with the exact scale exponent `1−n/a−epsilon`, for all a.e.-measurable real inputs. The restricted weak bound, operator measurability, L1/infinity bounds, both interpolation stages and measurable passage are proved. [LengthOperatorNorm.lean](LengthOperatorNorm.lean) covers the supremum over every length in a fixed positive interval and normed-valued inputs with each actual carrier volume in the denominator.

The constructive fractional seed includes every real m>1. Actual arbitrary-density localization, angular/spatial decomposition, marked pivot construction, collision estimates, cap thinning, cumulative-density conversion, two-ends removal and the recursive endpoint provide the full main chain. Intermediate implications retain the analytic hypotheses explicitly required by their source statements; the main endpoint supplies those inputs from proved seeds and earlier stages. [RadialSharpness.lean](RadialSharpness.lean) supplies the actual pencil construction for the recorded inverse-cap sharpness claim.

## Original proof routes completed

[GaussianNormalizedSeed.lean](GaussianNormalizedSeed.lean) closes the original source projection route: one actual Gaussian matrix simultaneously satisfies norm, noncollapse and collision bounds; its actual good-index graph yields a separated subset; one common map of the original grid labels supplies the projected family; the proved five-dimensional seed is applied to that same family; exact population accounting and cumulative/logarithmic conversion yield(2.2). No ambient-seven conclusion is substituted for that route and no custom Wolff axiom is needed.

[SamplingSourceProbability.lean](SamplingSourceProbability.lean) constructs the original raw probabilities, low/high alternative, physical ball tests and whole-sphere theta-net. The augmented high-cell/net test count is at most N^(ambient+2), the angular bound has the exact a0=64(ambient+4), and the angular and density/ball failure budgets are each strictly less than1/8 on the same raw law. Thus the probability of a positive-weight successful sample exceeds3/4. [SamplingSourceRealization.lean](SamplingSourceRealization.lean) packages that same J/net/outcome; [SphereNetSampleRealization.lean](SphereNetSampleRealization.lean) proves the original density band, quarter marked mass, relative xi/(8C0) mass, all-ball two ends, closed exact-theta cap broadness, positive original intersections, unchanged axes/caps/separation and original-grid support/union conclusions. No stronger narrow-density band is assumed.

[BushIteration.lean](BushIteration.lean) and [BushIterationConsequences.lean](BushIterationConsequences.lean) construct both prescribed appendix recurrences from actual bush base/lift inputs, every finite stage and each limiting arbitrary-position measurable endpoint for n>=5. The direct positive-p pivot handles the lifted exponents outside the narrower recursive-corollary range. [BushLengths.lean](BushLengths.lean) also proves the exact no-error cumulative bush inequality for bounded individual lengths, and [CumulativeLengths.lean](CumulativeLengths.lean) provides the general positive-error cumulative adapter.

## Qualifications and trust boundaries

The marked-pivot constant in [SourceMarkedLengths.lean](SourceMarkedLengths.lean) is chosen once for the fixed geometric normalization and used in both occurrences of the source minimum, including inside the1/alpha power. No comparison uniform in alpha with an independently preassigned different small constant is asserted. Constants need not be uniform as fixed positive length/width parameters tend to zero. The source-scope reviews state the interpretation and its mathematical basis.

Exactly three user-authorized Wolff/Katz–Tao/Zahl custom axioms remain, with explicit source-to-normalized-predicate translations. All7 dependent theorem declarations and all10 dependent declarations occur in ExternalAxioms. MainMaximal, MainOperator and all{new_since21} additions since checkpoint21 use only standard foundations. [AXIOMS.md](AXIOMS.md) and the registry describe the complete external trust boundary. Historical attribution, priority and literature-search exhaustiveness are not kernel theorems.

The supplied PDFs and audit were evidence, not instructions, and their bytes are unchanged. A Lean proof checks the formal statement and its dependencies; matching it to the manuscript is a separate source review. No claim of human expert certification or kernel verification of every prose sentence is made. The current [completion audit](reviews/checkpoint23_completion_audit.md) supersedes older remaining-work inventories. The verifier's final `scope` string describes logical-dependency checking without asserting manuscript coverage; consult the separate source completion audit for that correspondence.

## Reproduction and inventory

See [README.md](README.md), [MODULES.md](MODULES.md) and [verification/summary.json](verification/summary.json). One exact frozen snapshot was used throughout the build, audit and archive. Matching dependencies and the verified unchanged 406-module local build cache were reused; every exact module source was recompiled for the declaration audit. [Cache provenance](reviews/checkpoint23_build_cache_reuse.json) records the matching source boundary. A cold-cache build or fresh-machine download was not separately tested. No admitted proof, unsafe proof, native_decide proof or unregistered axiom is accepted.
''')

axiom_sections = []
for axiom in summary['external_axioms']:
    axiom_sections.append(f"### {axiom['name']}\n\nSource: [{axiom['source_locator']}]({axiom['source_url']}).\n\nFormal statement: `{axiom['formal_statement']}`.\n\nTrust boundary: {axiom['trust_boundary']}\n")
dependencies = '\n'.join(f"| `{name}` | {', '.join('`'+a+'`' for a in deps)} |"
    for m in summary['modules'] for name, deps in m['declarations_using_external_axioms'].items())
(stage / 'AXIOMS.md').write_text(f'''# Authorized published inputs

The user explicitly authorized Katz–Tao and other published results as custom axioms, superseding the earlier no-custom-axioms preference. Exactly three are declared in [ExternalAxioms.lean](ExternalAxioms.lean) and hash-registered in [external_axioms.json](external_axioms.json). No novel manuscript result is axiomatized.

{chr(10).join(axiom_sections)}

## All dependent declarations

The full audit reports7 dependent theorem declarations and10 dependent declarations in total, all within ExternalAxioms. MainMaximal, MainOperator and all{new_since21} new modules since checkpoint21 use only `propext`, `Classical.choice`, `Quot.sound`, or a subset. The generic normalized-shading adapter itself has an explicit premise and no custom dependency.

| Declaration | Registered dependency |
|---|---|
{dependencies}

See the [statement review](reviews/external_axiom_statement_review.md), [verifier review](reviews/external_axiom_verifier_review.md) and [complete dependency inventory](verification/summary.json). The exact source translations above are trusted assumptions; the subsequent adapters are proved. Katz–Tao's saturated recursion is not silently assumed for arbitrary-density novel inputs. The strict `--reject-external-axioms` option rejects the registered package by design.
''')

rows = '\n'.join(f"| [{m['module']}.lean]({m['module']}.lean) | {m['theorem_count']} | {m['audited_declaration_count']} | {'registered' if m['declared_external_axioms'] else 'standard'} |" for m in summary['modules'])
(stage / 'MODULES.md').write_text(f'''# Exact frozen source inventory

The module links are the delivered sources. The exact hashes and every declaration's logical dependencies are in [verification/summary.json](verification/summary.json). Generated and supporting declarations are counted separately from source theorem/lemma declarations.

| Module | Source theorem/lemma | All audited local declarations | Foundations |
|---|---:|---:|---|
{rows}
| **Total** | **{theorems}** | **{declarations}** | Three registered published axioms, isolated in ExternalAxioms |
''')

manifest = {str(p.relative_to(stage)): digest(p) for p in sorted(stage.rglob('*')) if p.is_file()}
(stage / 'output_manifest.json').write_text(json.dumps(manifest, indent=2) + '\n')
for rel, expected in manifest.items():
    assert digest(stage / rel) == expected, rel
with zipfile.ZipFile(staged_archive, 'w', zipfile.ZIP_DEFLATED) as z:
    for p in sorted(stage.rglob('*')):
        if p.is_file():
            z.write(p, Path(out.name) / p.relative_to(stage))
with zipfile.ZipFile(staged_archive) as z:
    assert z.testzip() is None
    expected = {str(Path(out.name) / p.relative_to(stage)): p for p in stage.rglob('*') if p.is_file()}
    assert len(z.namelist()) == len(set(z.namelist())) == len(expected)
    assert set(z.namelist()) == set(expected)
    for name, p in expected.items():
        assert z.read(name) == p.read_bytes(), name

# Keep the previous delivered artifacts as a local recovery copy.
backup = audit / 'checkpoint21_published_backup'
backup_archive = audit / 'checkpoint21_published_backup.zip'
assert not backup.exists() and not backup_archive.exists()
out.rename(backup)
archive.rename(backup_archive)
stage.rename(out)
staged_archive.rename(archive)
for name, expected_hash in frozen.items():
    assert digest(out / (name + '.lean')) == expected_hash
publication = {
    'checkpoint': 23, 'status': 'PASS', 'utc': datetime.now(timezone.utc).isoformat(),
    'modules': module_count, 'source_theorems': theorems, 'audited_theorems': local_theorems,
    'all_local_declarations': declarations, 'exact_checks': 131,
    'manifest_hashes': len(manifest), 'published_files': len(manifest) + 1,
    'zip_exact_inventory_and_bytes': 'PASS', 'registered_external_axioms': 3,
    'external_dependent_theorems': 7, 'external_dependent_declarations': 10,
    'old381_unchanged': True, 'old406_unchanged': True
}
(audit / 'checkpoint23_publication_validation.json').write_text(json.dumps(publication, indent=2) + '\n')
print(json.dumps(publication))
