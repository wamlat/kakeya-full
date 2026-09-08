#!/usr/bin/env python3
"""Assemble a source-coverage inventory only after the complete frozen audit passes.
The semantic obligations below are reviewed source comparisons; this script only
checks their exact source/declaration/evidence locators and release prerequisites.
"""
from pathlib import Path
from datetime import datetime, timezone
import hashlib, json, re, sys
A = Path(__file__).resolve().parent
D = A / 'formalization'
F = A / 'checkpoint23_verify'
sha = lambda p: hashlib.sha256(p.read_bytes()).hexdigest()
load = lambda p: json.loads(p.read_text())
frozen = load(A / 'checkpoint23_frozen_source_hashes.json')
assert len(frozen) == 427
requirements = []
def R(key, source, title, conclusion, proof, reviews='analytic geometry finite'):
    locators = []
    for item in proof.split():
        module, decl = item.split('.', 1)
        path = D / (module + '.lean')
        assert sha(path) == frozen[module] == sha(F / path.name), item
        pat = r'^[ \t]*(?:(?:private|protected|noncomputable)\s+)*(?:theorem|lemma|def|structure|abbrev)\s+' + re.escape(decl) + r'(?=\s|[:({])'
        matches = list(re.finditer(pat, path.read_text(), re.M))
        assert len(matches) == 1, (item, len(matches))
        locators.append({'module': module, 'declaration': decl,
                         'line': path.read_text()[:matches[0].start()].count('\n') + 1,
                         'source_sha256': frozen[module]})
    requirements.append({'id': key, 'source': source, 'title': title,
        'required_conclusion_and_scope': conclusion, 'proof_locators': locators,
        'semantic_reviews': [f'checkpoint23_{r}_completion_audit.md' for r in reviews.split()]})

R('C-T1.1', 'combined.txt:64-94', 'Theorem 1.1',
  'Every integer n>=6 has M_n(3+(2-sqrt2)(n-4)) for original completed-Lebesgue shadings at arbitrary positions; the constant precedes scale, density and family. Actual tube-volume sums and density exponent are retained.',
  'LebesgueMaximal.endpoint_formula LebesgueMaximal.estimate_iff_borel MainEndpoint.diagonal_discrete')
R('C-C1.1', 'combined.txt:145-185', 'Corollary 1.1',
  'The fixed single-error input at the same A and scale cutoff gives exactly one logarithm, unchanged error and density power, including empty, unequal and arbitrarily tiny rows. The separate all-errors input permits absorbing that logarithm.',
  'CumulativeFixedError.source_notation CumulativeFixedError.from_fixed_input CumulativeFixedError.linear_bin_budget CumulativeLengths.from_cumulative')
R('C-L2.1', 'combined.txt:219-279', 'Lemma 2.1',
  'The actual Gaussian projection from ambient7/cap4 to ambient5 produces the same-family cumulative lower bound c A^-1 N^(-1/2-eps) s^(7/2+eps) M; simultaneous norm, noncollapse and collision selection and original-label preservation are constructed.',
  'GaussianNormalizedSeed.source_count GaussianProjectedFamily.construct GaussianCollisionSelection.select', 'finite analytic')
R('C-T2.2', 'combined.txt:280-367', 'Theorem 2.2',
  'M6(4) implies M6(33/8); the conclusion is itself proved. The shading statement has no two-ends, angular, sampling or cap hypothesis.',
  'LebesgueMaximal.six_first_step LebesgueMaximal.six_first SixDimensionalUnrestricted.discrete')
R('C-L3.1', 'combined.txt:386-404', 'Lemma 3.1',
  'An actual common dyadic localization retains c M/log(2N)^2 original rows, actual ball restrictions, both density comparisons and all relative ball tests; original completed-measurable restrictions are separately constructed.',
  'SourceLocalizationGeometry.unit_source_notation SourceLocalization.construct LebesgueLocalization.exists_selection')
R('C-L3.2', 'combined.txt:415-421', 'Lemma 3.2',
  'Actual original tube assignments and restricted shadings have common angular/spatial scale, whole-carrier containment, cubic-log mass retention, pointwise broadness and overlap, including original bounded lengths and completed-measurable inputs.',
  'LebesgueAngularSpatial.construct MeasurableAngularSpatialLengths.construct')
R('C-L4.1', 'combined.txt:748-844', 'Lemma 4.1',
  'Fractional-direction arbitrary-shading seed for every real m>1 has the source scale/density powers and inverse-A dependence; thinning and localization are supplied by proofs.',
  'FractionalSeedFullRange.fractional_discrete_seed FractionalSeedFullRange.fractional_real_cap_seed')
R('C-L4.2', 'combined.txt:750-770', 'Lemma 4.2',
  'An actual integral leaf subset satisfies every descendant capacity and has at least the mass of a feasible fractional selection in a finite partition tree, including empty support and zero capacities.',
  'CapSelection.fractionalSelection CapSelection.all_capacities CapThinningGeometry.partitionTree')
R('C-C4.3', 'combined.txt:845-855', 'Corollary 4.3',
  'The source cumulative fractional seed covers unequal/empty original rows, every real m>1 and the literal requested scale/density error.',
  'FractionalSeedFullRange.source_cumulative FractionalSeedFullRange.fractional_cumulative_seed')
R('C-C4.4', 'combined.txt:856-870', 'Corollary 4.4',
  'An actual retained original direction subset has target h separation, population at least c A^-1(delta/h)^m M and fixed cap bound at h; whole original rows persist.',
  'CapThinningGeometry.full_cap_thinning LocalizedDirectionThinning.thin_to_scale')
R('C-T5.1', 'combined.txt:882-1319', 'Theorem 5.1',
  'The source-strength base/lifted analytic hypotheses give the original marked fourth-power estimate with exact kappa, xi, log, scale, density and population powers for p>0,q>=2 and the source smallness test. It retains these explicitly stated analytic premises. One source small constant is chosen after fixed geometric conventions and before alpha and all varying data.',
  'SourceMarkedLengths.source_notation SourceMarkedLengths.source_fourth SourceAnalyticInputs.Base.to_discrete SourceAnalyticInputs.Lifted.to_discrete')
R('C-L5.2', 'combined.txt:1283-1306', 'Lemma 5.2',
  'Given precisely the displayed precursor inequalities, the density and closing inequalities give (5.34), including q>=2 and the exact sigma-to-lambda and kappa losses. The actual energy consumer derives the closing precursor.',
  'ClosingEnergyAlgebra.source_density_combination ClosingEnergyAlgebra.source_from_energy ClosingEnergyAlgebra.error_kappa_weakening')
R('C-L6.1', 'combined.txt:1333-1496', 'Lemma 6.1',
  'The original raw incidence law yields the low/high alternative and a same-outcome realization of full density, quarter marked mass, relative marks, full ball tests, exact closed-cap broadness, unchanged geometry and original support. Both source failure budgets are <1/8 and success probability >3/4.',
  'LebesgueSamplingSource.source_sampling LebesgueSamplingSource.source_realization SamplingSourceProbability.source_sampling', 'finite geometry analytic')
R('C-P7.1', 'combined.txt:1497-1653', 'Proposition 7.1',
  'All-angle two-ends estimate follows from the actual base/lifted hypotheses over the full source positive-p range and sparse margin. Original arbitrary fixed density multiples and bounded individual lengths are allowed; no favorable marked or sampled output is a premise.',
  'SourceUnmarkedLengths.angular')
R('C-P8.1', 'combined.txt:1654-1702', 'Proposition 8.1',
  'Source absolute-cap unit-two-ends input globalizes for every C>0 to unrestricted inverse-A density exponent max(D,C), preserving the set exponent D. Actual localization, disjoint old-cell summation, direction thinning and measurable conversion are supplied.',
  'SourceAnalyticInputs.TwoEnds.globalize SourceAnalyticInputs.TwoEnds.globalize_measurable LebesgueRealCap.globalize SourceUnmarkedLengths.globalize')
R('C-C8.2', 'combined.txt:1703-1758', 'Corollary 8.2',
  'For 3<dprime<d<m, p>=d and q>=dprime, the actual K(m,d,p) and K(d,dprime,q) estimates imply K(m,(2m+3+dprime)/4,max(D,(p+2q+4)/4)); all-angle removal, cumulative lift and globalization are proved.',
  'UnrestrictedPivot.real_cap_pivot')
R('C-LA.1', 'combined.txt:1924-1964', 'Lemma A.1',
  'The no-epsilon cumulative bush lower bound c A^-1 delta^(m/2-1) s^((m+2)/2) M holds with arbitrary unequal/empty rows and without comparability or two-ends premises; bounded original lengths have an actual adapter.',
  'Bush.cumulative_bush_estimate BushLengths.cumulative')

R('F-main', 'first_step.txt:24-50', 'First-step proposed theorem',
  'The arbitrary original completed-measurable shading implication M6(4)->M6(33/8) is proved, with scale exponent15/8+eps and density exponent33/8; the literal strong operator bound is a separate proved consumer.',
  'LebesgueMaximal.six_first_step LebesgueMaximal.six_first MainOperator.six_first')
R('F-L1', 'first_step.txt:55-110', 'First-step Lemma 1',
  'The actual ambient7 to5 Gaussian route gives the inverse-A lifted cumulative input, including empty/unequal rows. A generic ambient7 seed is not substituted for the projection route.',
  'GaussianNormalizedSeed.source_count GaussianProjectionSeed.original_rows', 'finite analytic')
R('F-L2', 'first_step.txt:111-148', 'First-step Lemma 2',
  'Actual angular/spatial restriction, marked retention and pointwise broadness are constructed for the original family; subsequent good-mass pruning uses actual masks and proved fractions.',
  'LebesgueAngularSpatial.construct LebesgueDensityPruning.source_fractions')
R('F-L3', 'first_step.txt:149-213', 'First-step Lemma 3',
  'Continuous density-square hairbrush has the exact sqrt-cap and logarithmic losses, original measures and bounded individual lengths. Fine-scale raw marked formulas are retained separately, with their required scale tests.',
  'LebesgueSeedDensity.logarithmic_density_seed LebesgueSeedDensity.comparable_density_seed LebesgueHairbrush.broad_hairbrush_squared')
R('F-L4', 'first_step.txt:214-375', 'First-step Lemma 4',
  'The numerical six-dimensional marked core has kappa^58 xi^7 log^-8 N^(33/2-3e) lambda^(15+2e) S^3. Base and lifted estimates and actual collision/lift closing are proved; source normalization is explicit.',
  'SixDimensionalCore.marked_estimate SixDimensionalCore.base SixDimensionalCore.lift SourceMarkedLengths.source_notation Scalar.six_model_constants')
R('F-L5', 'first_step.txt:376-431', 'First-step Lemma 5',
  'The original measurable count-or-discretize alternative, source density band, quarter marks, two-ends, closed-cap broadness and physical old-grid support come from one actual raw-law outcome.',
  'LebesgueSamplingSource.source_sampling LebesgueSamplingSource.source_realization', 'finite geometry analytic')
R('F-L6', 'first_step.txt:432-530', 'First-step Lemma 6',
  'One constant chosen after fixed geometry,lengthUpper,c0,C0,B0,alpha,b,eps and before original N,lambda,M,F proves c N^(33/8-eps) lambda^(15/4)(M/N^5)<=E for ORIGINAL B0 log(2N)^b two-ends. The cap follows from separation; the density exponent remains15/4.',
  'SixDimensionalLogarithmicLengths.source_notation LogarithmicLengthEstimates.estimate WideLogarithmicTwoEnds.estimate LogarithmicTwoEnds.estimate')
R('F-L7', 'first_step.txt:531-574', 'First-step Lemma 7',
  'The same actual original localization has a dyadic witness, retained c M/log^2 population, both density bounds and every relative two-ends test. The source unit-width top cover is derived from actual midpoint geometry.',
  'SourceLocalizationGeometry.unit_source_notation SourceLocalization.dyadic_selection')

R('S-realcap', 'combined.txt:96-144; (1.3)-(1.5)', 'Real-cap and off-diagonal endpoint',
  'The real cap parameter is independent of integer ambient dimension. Every A>=1 is allowed after the uniform constant, all actual projective caps are tested, and the density envelope is max(P(m),4). Count and physical-volume Jacobians are correctly distinguished.',
  'LebesgueRealCap.real_cap_endpoint LebesgueRealCap.diagonal_volume MainEndpoint.real_cap_measurable')
R('S-pruning', 'combined.txt:463-538; (3.3)-(3.10)', 'Original-set good-mass accounting',
  'The same original survivor masks yield deletion<=W/8, surviving good mass>=3W/4 and retained good mass>=5W/8; density, relative two-ends, twice broadness, half marks and overlap follow for the same original completed-measurable sets.',
  'LebesgueDensityPruning.source_fractions SourceDensityPruningGeometry.surviving_two_ends SourceDensityPruningGeometry.marked_piece_broad SourceDensityPruningGeometry.retained_half_mass')
R('S-hairbrush', 'combined.txt:489-747; (4.4),(4.8),(4.11)-(4.16),(4.23)', 'Continuous and raw marked hairbrush',
  'The all-angle continuous sigma^2 A^-1/2 formula and both literal squared/unsquared marked fine-scale kernels are proved from actual tube intersections, plane bins and all-ball ends; a common null deletion preserves pointwise incidence.',
  'LebesgueSeedDensity.logarithmic_density_seed LebesgueHairbrush.broad_hairbrush_squared LebesgueHairbrush.broad_hairbrush_linear LebesgueHairbrush.real_cap_hairbrush_linear')
R('S-sharpness', 'combined.txt:833-844', 'Inverse-cap sharpness',
  'Actual separated radial-pencil configurations contradict uniform sublinear A loss in the stated real-cap range. Error is chosen before a proposed constant, and the physical counterexample exists at arbitrarily small scales.',
  'RadialSharpness.counterexamples RadialSharpness.no_uniform_sublinear_cap', 'finite geometry')
R('S-fibers', 'combined.txt:982-1282; (5.14)-(5.33)', 'Actual pivot fibers, collisions and closing',
  'Common angle fibers, legal output labels, attached endpoint samples, actual grouped lifted families and old-union support feed the energy lower bound. No desired collision, pruning or witness inequality is hidden in the final pivot input.',
  'AngleFiberSelection.select_angle_fibers ActualLabelSelection.construct CollisionEnergy.collision_energy_bound ClosingEnergyAlgebra.retained_grouped_closing SourceMarkedLengths.source_fourth', 'finite geometry')
R('S-sampling', 'combined.txt:1333-1496; (6.1)-(6.19)', 'Whole-sphere tests and exact raw law',
  'The original positive cell support and raw arrays are unchanged under Borel representatives; whole projective nets, exact N^(ambient+2) event budget and both <1/8 failures share the same product law. The same selected outcome has all physical conclusions.',
  'LebesgueSampling.data_eq LebesgueSampling.law_heq SamplingSourceProbability.source_sampling LebesgueSamplingSource.source_realization', 'finite geometry analytic')
R('S-measurable', 'combined.txt:1654-1758; section8.1', 'Original measurable and low-density conversion',
  'Actual cell intersection weights and original union volumes are used, including low-density and unequal-occupancy cases. Exact prescribed-mass subsets of original completed-measurable shadings are constructed with both endpoints allowed.',
  'LebesgueDensityTrimming.construct LebesgueMaximal.of_borel LebesgueRealCap.volume_of_borel LebesgueRealCap.lengths_of_borel')
R('S-diagonal', 'combined.txt:1759-1813; section9.1', 'Diagonal iteration and limits',
  'Actual finite-stage estimates and finite-depth error absorption prove the six/eight sequences and endpoints29/7,37/7. The endpoint is not obtained by substituting infinite depth into a configuration-dependent constant.',
  'LebesgueMaximal.six_diagonal_limit LebesgueMaximal.eight_diagonal_limit Scalar.diagonal_six_table Scalar.diagonal_eight_table')
R('S-realcap-iteration', 'combined.txt:1814-1875; section9.2', 'Real-cap iteration and density envelope',
  'Proved seed and pivot give actual finite real-cap stages. The recursion a_next=(2+a^2)/4 tends to2-sqrt2, and both set exponent and density envelope survive finite-depth passage to the endpoint.',
  'UnrestrictedPivot.real_cap_endpoint Endpoint.real_cap_endpoint_from_seed_and_pivot Scalar.slope_tendsto Scalar.density_envelope_bound')
R('S-operator', 'combined.txt:1876-1918; (9.7)-(9.8)', 'Literal strong maximal operator',
  'The supremum over actual original-position tube averages is measurable and satisfies the Mathlib eLpNorm bound C delta^(1-n/a-eps) for every a.e.-measurable real input. Both interpolation stages, measurable approximation and infinite norm cases are proved.',
  'MainOperator.endpoint_formula MainOperator.six_first OperatorNorm.Estimate', 'analytic')
R('S-lengths', 'combined.txt:53-64,96-109; fixed conventions', 'Individual lengths, volumes and operator denominators',
  'Actual bounded individual lengths and fixed widths/separations are transported with common dilation and proved volume Jacobians. Original tube-volume sums and individual operator-average denominators are retained; constants precede the original configuration.',
  'LebesgueMaximal.length_endpoint_formula LebesgueRealCap.lengths_of_borel LengthOperatorNorm.endpoint_formula LengthOperatorNorm.six_first', 'analytic geometry')
R('S-bush-iterations', 'combined.txt:1965-2036; AppendixA.2-A.3', 'Both prescribed bush iterations',
  'Actual ambient-(n+1) bush lifts and the positive-p pivot prove both prescribed finite recurrences and n>=5 limits(4n+4)/7 and(4n+3)/7, retaining the distinct set/density exponents. The generic measurable/length adapters give their original-set conclusions.',
  'BushIteration.bush_stage BushIteration.weakened_bush_stage BushIteration.bush_endpoint BushIteration.weakened_bush_endpoint BushIterationConsequences.bush_endpoint_maximal LebesgueMaximal.lengths_of_borel', 'finite analytic')
R('S-benchmarks', 'combined.txt:2037-end; AppendixB', 'Exact benchmark maximum, table and conversions',
  'The finite max-min formula over every integer2<=ell<=n gives each listed exact rational benchmark. Rational radical bounds prove comparison signs and all adjoint fractions. Printed decimal formatting is separately checked numerically.',
  'Scalar.benchmark_five Scalar.benchmark_six Scalar.benchmark_fifteen Scalar.benchmark_comparison_signs Scalar.benchmark_adjoint_conversion Scalar.sqrt_two_rational_bounds', 'finite analytic')
R('S-five-caveat', 'combined.txt:83-94; AppendixB', 'Dimension-five envelope restriction',
  'The numerical five-dimensional real-cap profile has density envelope4; no diagonal M5 assertion is inferred below that envelope.',
  'Scalar.dimension_five_envelope_is_four Scalar.diagonal_envelope_obstruction', 'finite analytic')
R('S-conventions', 'combined.txt:53-64,96-109,898-912', 'Metric and marked small-constant conventions',
  'Actual chord/projective-angle comparison is proved. The marked source small constant is existentially chosen once for fixed normalization and used in both positions of its minimum, before alpha and all varying data. No alpha-uniform comparison with a distinct preassigned constant is asserted.',
  'ProjectiveAngleComparison.chord_angle_bounds ProjectiveAngleComparison.cap_comparison SourceMarkedLengths.source_notation MinPivotLogBudget.source_notation', 'geometry analytic finite')

if '--check-locators' in sys.argv:
    print(json.dumps({'status':'LOCATORS_CHECKED_NOT_PROOF_VERIFICATION', 'requirements':len(requirements), 'numbered_combined':17, 'first_step':8, 'supplementary':len(requirements)-25}))
    sys.exit(0)
summary_path = A / 'checkpoint23_verification/summary.json'
summary = load(summary_path)
assert summary['status'] == 'PASS'
assert len(summary['modules']) == len(frozen) == 427
assert summary['exact_named_checks'] == 131
assert len(summary['external_axioms']) == 3
assert summary['theorems_using_external_axioms'] == 7
assert summary['declarations_using_external_axioms'] == 10
standard = {'propext','Classical.choice','Quot.sound'}
module_audits = {m['module']:m for m in summary['modules']}
assert set(module_audits) == set(frozen)
for name,m in module_audits.items():
    assert m['source_sha256'] == frozen[name] == sha(D/(name+'.lean')) == sha(F/(name+'.lean'))
    assert m['compiler_exit_code'] == 0
    if name != 'ExternalAxioms':
        assert set(m['axioms']) <= standard
        assert not m['declarations_using_external_axioms']
for r in requirements:
    r['status'] = 'proved'
    for loc in r['proof_locators']:
        m = module_audits[loc['module']]
        matching = {k:v for k,v in m['declaration_dependencies'].items() if k == loc['declaration'] or k.endswith('.'+loc['declaration'])}
        assert len(matching) == 1, (r['id'],loc,matching)
        name,deps = next(iter(matching.items()))
        assert set(deps) <= standard
        loc['audited_name'] = name
        loc['logical_dependencies'] = deps
reviews = {f'checkpoint23_{label}_completion_audit.md':sha(A/f'checkpoint23_{label}_completion_audit.md') for label in ['finite','geometry','analytic']}
indexes = {f'checkpoint23_{label}_completion_hashes.json':sha(A/f'checkpoint23_{label}_completion_hashes.json') for label in ['finite','geometry','analytic']}
reg = load(A/'checkpoint23_regression_results.json')
assert reg['status']=='PASS' and reg['case_count']==12
assert reg['verifier_sha256']==sha(F/'verify.py')
assert sha(F/'verify.py')==load(A/'checkpoint23_freeze.json')['verifier_sha256']
source_manifest = load(A.parent/'outputs/kakeya_verification/source_manifest.json')
for source in source_manifest['sources']:
    assert sha(Path(source['path']))==source['sha256']
qualifications = [
    'Coverage is mathematical source-statement correspondence under the documented fixed conventions; it is a semantic review, separate from kernel checking.',
    'The marked small constant is chosen existentially for fixed normalization before alpha and all varying parameters; uniform comparison to a distinct preassigned constant is not asserted.',
    'Ceiling capacities, a complement-graph independent-set argument, selected rounded projection labels and an exact induced finite product law are sufficient proved alternatives to the corresponding prose methods.',
    'Historical attribution, priority, exhaustive literature comparison and the proofs within cited papers are not newly formalized. Exactly three authorized published normalized inputs remain explicit optional custom axioms, isolated in ExternalAxioms; no listed main or new source consumer depends on them.',
    'Decimal display QA and the separate exact-check script are auxiliary checks; exact rational/radical theorem statements are kernel checked.',
    'The reviews were produced within the same AI-assisted development process and are not independent human expert endorsements.',
    'Matching installed dependencies and the verified unchanged406 local build cache were reused. Every exact module source was recompiled for the declaration audit. Cold-cache setup/downloading was not separately tested.'
]
evidence = {'checkpoint':23,'status':'PASS','scope':'mathematical_source_coverage','utc':datetime.now(timezone.utc).isoformat(),
  'frozen_source_hashes_sha256':sha(A/'checkpoint23_frozen_source_hashes.json'),
  'verifier_sha256':sha(F/'verify.py'),'integrated_summary_sha256':sha(summary_path),
  'source_documents':source_manifest['sources'],'semantic_reviews':reviews,'review_indexes':indexes,
  'numbered_combined_results':17,'first_step_main_and_lemmas':8,'supplementary_requirements':len(requirements)-25,
  'requirements':requirements,'remaining_source_requirements':[],'qualifications':qualifications,
  'release_boundary':'The complete427 integrated verifier and12 verifier regressions passed. Archive construction and final byte validation are separate publication gates.'}
(A/'checkpoint23_completion_evidence.json').write_text(json.dumps(evidence,indent=2)+'\n')
rows=[]
for r in requirements:
    refs=', '.join(f"[{p['module']}.{p['declaration']}](../{p['module']}.lean#L{p['line']})" for p in r['proof_locators'])
    rows.append(f"| {r['title']} ({r['source']}) | {r['required_conclusion_and_scope']} | {refs} |")
text=f'''# Final mathematical source completion audit — checkpoint23

All17 numbered results in the combined PDF and the first-step theorem and seven lemmas now have actual proved consumers or explicit compositions under the documented source conventions. The {len(requirements)-25} additional requirements below cover intermediate quantitative assertions, endpoint iterations, operator bounds and appendices. This is a positive requirement inventory, not an inference from theorem counts or a percentage of correctness.

The final427-module build and declaration audit passed at {summary['utc']}: **{summary['theorem_count']} source theorem/lemma declarations**, **{summary['audited_theorem_count']} audited theorem declarations**, **{summary['audited_declaration_count']} all local declarations**, and **131 exact checks**. All12 verifier regression fixtures passed against the exact delivered verifier hash. The companion [evidence index](checkpoint23_completion_evidence.json) binds each entry below to its exact frozen module bytes and audited declaration dependencies, and records the source-document and review hashes.

## Main entry points

[LebesgueMaximal.six_first](../LebesgueMaximal.lean) proves the original completed-measurable shading assertion M6(33/8); `six_first_step` proves M6(4)→M6(33/8). The same module supplies the full n>=6 endpoint and individual-length variants. [MainOperator](../MainOperator.lean) proves the literal strong maximal-operator assertions. These are part of a427-module project and need their imported dependencies.

## Requirement-by-requirement coverage

| Source conclusion | Required scope positively checked | Exact proved route |
|---|---|---|
{chr(10).join(rows)}

## Last source gaps closed

The frozen406 review identified a missing public fixed-single-error/one-log conclusion and Borel-only intermediate interfaces. The later418 source comparison identified a dyadic localization witness that needed to remain attached to the actual selection and the first-step logarithmic two-ends uniformity. The underlying cumulative finite-bin proof already existed; its every-error public wrapper did not itself supply the separate fixed-error conclusion. Checkpoint23 supplies the literal one-error/one-log corollary, exact completed-measure original-set consumers, the joint actual dyadic/count/density certificate, and the full original logarithmic-B consumer with fixed density multiples and bounded individual lengths. In the last theorem, the local two-ends coefficient is fixed before the estimate is applied; the original varying coefficient is handled by an actual localization radius inequality and a proved logarithmic loss. Its density exponent remains15/4.

The [finite](checkpoint23_finite_completion_audit.md), [geometry](checkpoint23_geometry_completion_audit.md) and [analytic](checkpoint23_analytic_completion_audit.md) reviews inspect the detailed source predicates and constructions. Their indexes distinguish historical418 references from the final427 freeze. The six additional typed Appendix/completed-measure compositions are included as [signature checks](checkpoint23_analytic_signature_checks.lean); they compile clean and are auxiliary evidence, not unregistered production modules.

## Qualifications and trust boundary

'''+''.join('- '+q+'\n' for q in qualifications)+f'''
No identified substantive mathematical source requirement remains in this inventory. This does not certify every prose sentence or claim an exhaustive literature audit. The semantic source comparison is separate from Lean's verification of the exact formal statements.

## Release evidence

The [integrated summary](../verification/summary.json) has SHA256 `{sha(summary_path)}`. The [427-source hash manifest](checkpoint23_frozen_source_hashes.json) has SHA256 `{sha(A/'checkpoint23_frozen_source_hashes.json')}`. The [verifier review](checkpoint23_verifier_review.md) records the metadata-only correction and unchanged checking logic. [Cache provenance](checkpoint23_build_cache_reuse.json) records precisely what was reused. The final output manifest and ZIP must also be checked against these bytes before release; that publication validation is recorded separately.
'''
(A/'checkpoint23_completion_audit.md').write_text(text)
print(json.dumps({'status':'PASS','requirements':len(requirements),'modules':len(frozen),'summary_sha256':sha(summary_path)}))
