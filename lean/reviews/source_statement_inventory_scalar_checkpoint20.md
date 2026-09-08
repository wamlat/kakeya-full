# Independent source-statement inventory after checkpoint 19

This is a read-only statement audit against `source/combined.txt` and `remaining_paper_results_checkpoint19.md`, updated for the new source-minimum pivot, literal raw sampling, measurable square-root-cap seed, projection conclusion and Appendix endpoints. The locators below are line numbers of the extracted `combined.txt`; printed equation and section numbers are also supplied. I inspected the actual theorem signatures and relevant definitions, rather than treating module names or proof counts as coverage evidence. I did not modify Lean sources, the verifier or the published package.

The main maximal-shading and strong maximal-operator conclusions remain proved. The completed development extensions now close the previously identified analytic-input mismatch for Theorem 5.1, the full positive-p and fixed-comparability scope of Proposition 7.1, and the absolute-cap/small-scale-input and full density scope of Proposition 8.1. **The separate marked normalization in literal Theorem 5.1 still requires its own argument.** The measurable spatial Lemma 3.2 has now been constructed for unit original axes; the fixed comparable-length extension remains under separate development. These are statement-scope distinctions, not discovered contradictions or kernel failures.

**Final development-source update:** the new exact predicates `SourceAnalyticInputs.Base`, `.Lifted` and `.TwoEnds` only require eccentricity N>=2 and match the source absolute-cap or paired-error cumulative inputs. Their proved adapters use actual unchanged-scale whole-tube thinning, an actual cumulative object, integer density/error transfer, and actual large-mesh completion. `SourceMarkedPivotSmallScaleInputs` exposes the source marked conclusions under those exact inputs, while retaining an explicit strict marked normalization. The fourteen modules recorded in `positive_angular_range_progress.md` and `positive_angular_range_audit.json` are frozen and individually audited standard-only; `PositiveWideTwoEndsPivot.from_source_inputs` has all p>0 and arbitrary fixed lower/upper original density multiples and positive geometric separation, with no angular or marked premise. `SourceAnalyticInputs.TwoEnds.globalize` and `.globalize_measurable` expose Proposition 8.1 from its literal source input, including 0<C<1. The new independently reviewed `OriginalLowerDensity.globalize` additionally handles arbitrary fixed original lower density multiples, with no upper-density or original two-ends premise. `MeasurableAngularSpatial` provides actual original-index spatial groups, containing finite-length tubes, proportional marked restoration, broadness and overlap for arbitrary-position measurable unit-tube shadings. Its variable-length extension is not asserted here.

These additions are candidates for integrated checkpoint 20. An individual clean compile or source audit does **not** make a source part of the previously published checkpoint 19. The detailed historical discussion below is retained to explain the precise distinctions and what the new adapters close; current status is stated in the table and this update. The parent owns full package verification and publication.

## Numbered conclusions

| Source and exact locator | Actual proved API and scope | Assessment |
|---|---|---|
| Theorem 1.1, (1.1)–(1.2), lines 49–85; real-cap and diagonal limits in §9.1–9.2, lines 1759–1874 | `MainEndpoint`, `MainMaximal.endpoint`, `.endpoint_formula`, `.six_first`, `.six_first_step`, `.six_endpoint`, `.eight_endpoint`, `.six_diagonal_limit`, `.eight_diagonal_limit`; `UnrestrictedPivot.real_cap_endpoint` | Main shading conclusions are covered, including actual measurable unions, actual tube volumes and arbitrary tube positions. No supplied seed/pivot/sampling conclusion or external-result axiom is needed. The diagonal 29/7 and 37/7 bounds follow from the stronger proved endpoint by valid diagonal weakening. |
| Corollary 1.1, lines 145–186 | `Cumulative.finite_bin_bound` in `CumulativeEstimate.lean`; `DiscreteEstimate.to_cumulative`; `RealCapEstimate.to_cumulative` | The actual finite bin estimate has one factor `J+2` on the union side, not a density-dependent number of classes. It includes an empty class, unequal shadings and arbitrarily small cumulative density. Its fixed grid-normalization factor is explicit in the density. The uniform every-positive-error conclusion follows by the proved logarithmic absorption. |
| Lemma 2.1, (2.2), lines 219–278 | New `ProjectionConclusion.source_cumulative` and `.source_count` | The literal cumulative conclusion is now exposed: `c A⁻¹ N^(-1/2-e) s^(7/2+e) M ≤ E`, constants before all configurations, including empty shadings and arbitrary nonnegative cumulative density. This follows from the proved fractional seed. The Gaussian projection proof is a separate, still unformalized route. |
| Theorem 2.2, (2.5)–(2.6), lines 280 onward | `SixDimensionalUnrestricted`, `MainMaximal.six_first`, `.six_first_step` | The actual 33/8 conclusion is proved outright, hence also the stated implication from M6(4). The formal proof need not assume Wolff's theorem or reproduce the Gaussian route to establish this conclusion. |
| Lemma 3.1, (3.1), lines 386–403 | `FiniteGridLocalization.exists_selection`; `CommonDensityLocalization.exists_selection`, `.Selection.common_mass_lower`, `.Selection.density_depth_log_bound`; `MeasurableRescaling.localized_volume_upper`; `LocalizedSeedNormalization.localized_card_upper`; `LocalizedCellPartition` | The essential literal localization properties are proved: common radius, common density, population fraction with two logarithmic class counts, **density lower bound without an additional logarithm**, actual ball support and relative two ends. Finite and measurable localization are both present. The geometric volume/cardinality upper bounds give density `O(rho)`. The source permits a fixed enlargement of the top radius; the generic APIs make their initial radius-one cover explicit. Actual geometric cover/normalization adapters exist in the application chain. |
| Lemma 3.2, lines 415–463 | `SpatialAssignment.discrete_angular_spatial_decomposition`; `MeasurableAngularPieces.exists_pieces`; new `MeasurableAngularSpatial` | The discrete angular and spatial statement is constructed. The new arbitrary-measurable unit-axis construction gives disjoint original-index angular/spatial groups, original-set restrictions, full carriers in explicit finite-length `parallelBox`/`lengthCarrier` containers, fixed broadness, overlap `C tau^(-beta)`, and stronger `c/(J+1)` retained mass. Fixed comparable-length original axes remain a separate extension; they are not silently identified with unit axes. |
| Lemma 4.1 and Corollary 4.3, (4.29), lines 748 and 845–855 | `FractionalSeedFullRange.fractional_discrete_seed`, `.fractional_real_cap_seed`, `.source_cumulative` | Covered throughout the literal real range `m>1` (hence its subrange `1<m≤ambient-1`), including cumulative unequal/empty shadings and the exact positive scale/density errors. The older `m>3` restriction is no longer a standalone gap. |
| Lemma 4.2, lines 750–783 | `CapacityTree.fractionalSelection`, `.all_capacities` in `CapSelection.lean` | Actual arbitrary finite arity rooted partitions and all integer node capacities are handled. The subset is constructed by a proved integral-rank argument; desired rounding is not assumed. |
| Corollary 4.4, lines 856–869 | `CapThinningGeometry.full_cap_thinning`; `SeparationColoring.full_separation_coloring` and large-color extraction | The actual cap-preserving selection is proved. The direct thinning theorem has separation `2r/(k+1)`, retention `M/[C(k,m) A (r/delta)^m]` and every-scale cap `C(k,m)(u/r)^m`. If the word “h-separated” is interpreted literally with coefficient one, the already proved fixed separation coloring supplies it at a further fixed loss. The source allows fixed separation changes. No laminar or cap-cover oracle remains. |
| Theorem 5.1, (5.3), lines 879–944 | `SourceMarkedPivotFullRange`; new `SourceMarkedPivotSmallScaleInputs`; `MinPivotKappa.sourceChoice` | The exact fourth-power exponents, literal minimum kappa, natural logarithm and sole large `N*kappa^20` cutoff are assembled for every p>0. The new wrapper takes exactly the source N>=2 absolute-cap base and paired-error cumulative lift inputs. **Its original marked density/separation normalization remains stricter than the literal fixed-normalization conventions.** The unmarked wide-density adapter does not claim to fix this separate issue. |
| Lemma 5.2, (5.34), lines 1283–1301 | `ClosingEnergyAlgebra.source_density_combination`, `.source_from_energy`; `PivotFourthPower`; the actual selected-output/positive pivot assembly | The scalar density accounting is proved with the displayed kappa, lambda, scale and logarithmic powers. Its uses in the actual fourth-power theorem are instantiated by constructed fibers, selected lifted outputs and the proved energy bounds; an arbitrary (5.33) is not assumed by that theorem. |
| Lemma 6.1, (6.1)–(6.11), lines 1333–1490 | `SamplingParameterRange`, `SamplingLengthInput`, `SamplingLengthAssembly.construct`, `SamplingLengthRealization.construct` and `.Output` theorems; `SamplingClosedCaps` | **The full literal sampling statement is covered.** Arbitrary fixed `0<s<1`, `0<alpha<1-s`, original raw probabilities, arbitrary fixed width/axis-length bound/positive direction separation, exact original axes/grid/marks and the source theta are present. Details below. |
| Proposition 7.1, lines 1497–1649 | New `PositiveWideTwoEndsPivot.from_source_inputs`, through fourteen audited positive-range/wide-row modules | The full p>0 range is now proved under the literal N>=2 source analytic inputs and displayed D/C/margin hypotheses. Original geometry is arbitrary fixed normalization; full rows can have any fixed positive lower/upper density multiples. The actual every-row trimming has only a fixed two-ends cost and precedes construction of marks. All angular pieces, four local cases and original-cell summation are constructed. No marked or outcome oracle appears in the public theorem. |
| Proposition 8.1 and §8.1, lines 1654–1757 | New `SourceAnalyticInputs.TwoEnds.globalize`, `.globalize_measurable`; `OriginalLowerDensity.globalize` | Actual localization/grouping/thinning/rescaling/summation and measurable passage now consume the literal absolute-cap N>=2-only source premise. Every source C>0 is included, with set exponent D and density exponent max(D,C). `OriginalLowerDensity.globalize` explicitly permits arbitrary fixed original lower density multiples, without an upper-density bound or any original two-ends condition. Fixed constants precede every actual configuration. |
| Corollary 8.2, (8.2), lines 1703–1716 | `UnrestrictedPivot.real_cap_pivot` | The exact source recursive K implication is proved for `3<d'<d<m`, `p≥d`, `q≥d'`, in every adequate integer ambient dimension. The K hypotheses themselves are full real-cap estimates, so the weaker-premise conditional distinctions above do **not** leave a gap in this corollary or the main iteration. |
| Lemma A.1, lines 1924–1963 | `Bush.cumulative_bush_estimate` | Literal cumulative bush bound with `m>0`, fixed width, arbitrary unequal/empty shadings, linear inverse cap coefficient and no scale error. It needs no separation or two-ends premise. It is not a missing seed. |

## Quantitative statements outside the numbered theorem list

- **Continuous all-angle square-root-cap estimate (4.4), lines 546–574 and 690–744:** the new `MeasurableSeedDensityLengths.logarithmic_density_seed` states the exact normalized-volume bound `c/sqrt(A) * log(2/delta)^(-P) * sigma^2 * M * delta^((m-3)/2)`. Its constants are chosen before actual scale, density, A, population, positions, shadings and individual lengths. Arbitrary fixed positive separation and length upper bound, fixed width, fixed or logarithmic upper/lower density ratios and logarithmic full-two-ends constants are permitted. `comparable_density_seed` is its ordinary fixed-ratio specialization. A positive lower length bound is unnecessary for this stronger formulation, so comparable axis lengths are included. These sources and oleans were present when inspected; publication still requires the parent's final exact-source audit and package verification.
- **Radial sharpness, lines 833–844:** `RadialPencil` and `RadialSharpness` give actual geometric counterexamples to replacing unrestricted `A^-1` by `A^-gamma`, `gamma<1`. The scale-error budget is fixed before the proposed constant; sufficiently fine original-cell pencils violate it. This does not contradict the valid fixed-two-ends square-root-cap estimate.
- **§9.3, (9.7)–(9.8), lines 1876–1911:** `OperatorRestrictedWeak`, `RestrictedStrong`, `StrongInterpolation`, `OperatorNorm`, `MainOperator` prove the actual indicator restricted-weak and strong `eLpNorm` conclusions for the supremum over all original unit-tube positions. Both interpolation stages, endpoint inputs, output measurability and measurable approximation are proved, rather than supplied as an analytic oracle.
- **Appendix A.2/A.3, lines 1965–2060:** `AppendixEndpoints.bush_discrete`, `.weakened_bush_discrete`, `.bush_maximal`, `.weakened_bush_maximal` now expose both endpoint conclusions for every integer `n≥5`, including n=5. They use a stronger proved seed/endpoint and valid diagonal weakening. The separate optional bush iteration route is not needed for these conclusions.
- **Appendix B, lines 2064–2106:** the rational/radical comparisons and dimension-five caveat are checked in `Scalar`. The larger dimension-five profile is not a manuscript diagonal conclusion and must not be listed as an omitted new result. Historical published theorem and Hausdorff-dimension attributions remain source/provenance matters, not new theorems claimed proved by the main kernel chain.

## Historical boundary analysis and residual marked normalization

The following subsections preserve the original signature comparison. Analytic-input, positive-p, and unmarked wide-density boundaries have since been closed by the modules in the current-status table; they are no longer listed as remaining gaps. The marked Theorem 5.1 normalization is still separate. The measurable spatial discussion identifies the earlier missing field, now constructed for unit axes only.

### Theorem 5.1: weaker analytic hypotheses (subsequently closed)

Source (5.4), immediately after the theorem, is an estimate on **absolute-cap** comparable families, with every positive scale loss. Source (5.5) is an estimate on arbitrary cumulative lifted shadings, with uniform `A^-1` and paired errors `N^-e * s^(q+e)`.

At the inspected hash, every public theorem in `SourceMarkedPivotFullRange` instead takes:

```
hbase : DiscreteEstimate (k+2) m d p
hlift : DiscreteEstimate (k+3) d d' q
```

`DiscreteEstimate` (`Configurations.lean:93`) quantifies all normalizations and all actual cap coefficients A, uniformly with `A^-1`; its density exponent has no error. Thus the formal source-style theorem proves the exact conclusion **from stronger inputs**. Writing “literal Theorem 5.1 is completely covered” without this qualification is premature.

Two independent adapters can plausibly close this logical scope, but are not supplied merely by reading an asymptotic convention:

1. Absolute-cap base estimates imply uniform inverse-cap estimates by actual whole-tube cap-preserving thinning at unchanged scale. The input constant must be fixed before A and configurations; the output cap constant is fixed geometrically.
2. The source paired-error cumulative lifted input implies the required comparable `DiscreteEstimate(q)`: on positive comparable integer shadings, `lambda≥delta/2` allows `lambda^e` to be absorbed into a second scale error, with source e chosen before configurations. Empty families and the fixed coarse scale range must be handled as well.

The parent assigned these adapters separately while this inventory was being completed. They are not counted as completed here before their resulting theorem statements are inspected.

### Theorem 5.1: fixed geometric and row normalization

`AdmissiblePivotSlabs.Hypotheses` (`:17–45`) uses the actual original family, cover, marks, cap bound and full all-radius two ends. It imposes exactly:

- `F.Separated delta`, rather than fixed `c*delta` separation;
- `F.Comparable delta lambda`, defined by `lambda/delta ≤ #Y_i ≤ 2*lambda/delta`;
- open projective theta-caps at marked cells with the literal one-tenth bound.

Source lines 879–899 permit fixed positive separation and arbitrary fixed positive lower/upper comparable-density constants. Source 1.1 also permits fixed geometric changes. The public source-minimum theorem does not yet construct this marked normalization. Selecting a color or density class can alter the marked row and destroy its one-tenth broadness, so it is not valid simply to invoke an unmarked fixed-loss subfamily principle. The raw sampling theorem's wider density band does not itself close this marked-core bridge. A direct generalized core or a proved marked-preserving normalization is needed.

The width restriction `width≥1/12` is different: increasing the fixed admissibility width to `max width (1/12)` preserves the original cells, directions and marks. The theorem's source kappa constant is then a fixed geometric constant. Its use of `alpha>0` is broader than source `0<alpha≤1`, and its `0<e≤1` includes the source range `0<e<1`. The cap coefficient A0 is fixed before the configuration in `.source_union`, exactly as required to absorb it into the final source constant. Neither B nor theta nor alpha is hidden in that constant.

`MinPivotKappa.sourceChoice = c(width)*min(theta,1/100,(c(width)/B)^(1/alpha))` is genuinely the source minimum. The normalized inequality has the exact source powers `5(ambient-1)+6q+12`, `xi^(p+3)`, `log(2N)^(-(p+4))`, `N^(2m+3+d'-3e)`, `lambda^(p+2q+4+2e)` and `(M/N^m)^3`. No product-to-minimum comparison is being used.

### Proposition 7.1: 0<p<1 (subsequently closed, including fixed density multiples)

The source allows every p>0 consistent with the displayed D, C and positive-margin conditions. `AllAnglePivot.all_scales` (`:92`) and `TwoEndsPivot.from_base_and_lift` (`:15`) still explicitly require `1≤p`. The new positive-density trimming and `SourceMarkedPivotFullRange` have removed that restriction from the marked fourth-power estimate, but not yet from the sampled marked estimate and final angular assembly. No claim is made here that actual source analytic inputs with p<1 exist; the point is the stated logical parameter range of the conditional proposition. The parent assigned a separate extension after this audit.

### Proposition 8.1: absolute-cap input and C<1 (subsequently closed)

The source premise at lines 1654–1664 is only an absolute-cap two-ends estimate for each fixed exponent/constant. `TwoEndsDiscreteEstimate` quantifies every actual A with a uniform inverse-cap coefficient. `TwoEndsGlobalization.remove_two_ends` consumes that stronger predicate. Its localized normalized families do have a fixed cap constant, and actual thinning is available, but the weaker-premise public adapter is not the same theorem signature. The finite agent has been assigned that adapter.

The remaining positive density range `0<C<1` needs only a short proved composition: on `0<lambda≤1`, the input power C implies power one; because D>1, `max(D,1)=max(D,C)=D`. This is a statement wrapper, not a missing geometric reduction.

### Lemma 3.2: measurable spatial containment (now constructed for unit axes)

`MeasurableAngularPieces.Pieces` has common scale, measurable original-set restrictions, a unique angular assignment, local cap, mass retention, fixed broadness and pointwise overlap. It has no spatial label or containing tube/box field. Its actual continuous hairbrush consumers use a kernel with no bounded-position premise, so they correctly avoid spatial subdivision. Consequently the **continuous (4.4) conclusion can be proved even while the standalone measurable spatial conclusion of Lemma 3.2 remains unassembled**.

The corresponding finite theorem `SpatialAssignment.discrete_angular_spatial_decomposition` explicitly constructs the spatial labels, actual containing `parallelBox`, proportional restoration and overlap. For arbitrary measurable shadings one still needs a measured spatial split/restoration on the same weighted incidence-pattern construction, or an equivalent direct measurable assignment. The parent assigned that extension separately. This is not a missing Gaussian/alternative route; spatial containment is part of the literal lemma's conclusion.

### Section 3 refinements: do not assume broadness inheritance

The finite chain `AngularRestrictedRefinement.construct`, `AngularRestrictedMeasurable`, `SpatialMarkedPartition`, `AngularRefinementBudgets` and `AngularSpatialBudgets` constructs the actual selected full shadings, density class and marked subsets. It proves their changed broadness and two-ends constants and inverse-log density/population/marked budgets. In particular its full output is the selected restricted angular shading, not silently restored to the original larger shading.

The measured `MeasurableDensityRecovery` and `MeasurableMarkedSelection` integrate actual finite multiplicities to prove discarded-mass bounds and proportional marked recovery. These supply the needed density/marked functionality. The exact intermediate fractions `3W/4` and `5W/8` of source (3.9)–(3.10) are not all exposed together as one named Section-3.3 theorem; downstream proofs use explicit adequate fixed fractions from these proved constructions. This is an alternative bookkeeping route to the required estimates, not evidence that the final estimates lack mark restoration. The missing containing spatial tube for arbitrary measurable pieces remains the distinct boundary above.

## Newly closed raw sampling scope

The final sampling realization uses exactly `rawFull Full delta ...` and `rawMarked Full G delta ...`, defined by original physical cell-intersection volumes divided by `delta^ambient`. Its certificate holds one original coupled outcome. It does not replace these arrays by equalized row probabilities.

- The low alternative gives the source positive-low-cell mass and count with literal `Wg/2` and `Wg/(2*a0*log(2/delta))`.
- The high alternative supplies actual original-index shadings with the stronger narrow mean band; the displayed source `[c0/2,2C0]` density band follows. Marks retain `Wg/4`, and the source comparison with `xi/(8C0)` times the full incidence sum is proved.
- `SamplingClosedCaps` proves a strict diameter bound for a closed projective theta-cap of unit directions when `theta≤1`. Hence the existing open `2*theta` tests imply closed **theta** broadness with the source theta itself. No factor-two radius replacement is needed in the output.
- The original positive separation, cap coefficient/exponent and every axis are unchanged. The physical carrier uses the original interval `[0,length_i]`; a fixed upper length suffices, hence any fixed comparable-length class is included.
- Output cells have their own positive full intersections. Their union is inside the available cell union and their count is at most that support's count; it is not asserted that whole selected cells lie inside the original measurable union.
- The uniform failure budget uses the positive gaps `1-s` and `1-s-alpha` and actual polynomial test counts. The source's B and xi inverse-log assumptions are more than is needed for existence of this raw low/high alternative; the actual K budget is used to place the angular test radius above the mesh. No realized outcome or small failure probability is supplied by the caller.

## Alternative proof routes, not missing conclusions

The Gaussian 7-to-5 map, its small-ball collision probability, simultaneous random realization and projected-cell comparison in (2.3)–(2.4) are not constructed. `ProjectionConclusion` proves their advertised lifted union conclusion by a different proved seed. Likewise the optional Appendix A bush iterations are not fully instantiated stage by stage, but their endpoint statements now have direct proved wrappers. Neither absence justifies saying the corresponding endpoint or cumulative conclusion is unproved.

The prior checkpoint-19 inventory should therefore be updated rather than copied unchanged: its literal sampling, continuous square-root-cap density/geometry, p>0 minimum-kappa assembly, named projection-conclusion and Appendix-endpoint gaps have materially advanced or closed. Its “core applications covered” wording for §§3,7,8 should retain the finer standalone distinctions identified above.

## Source-byte record

All following `.olean` files were present at inspection. Presence alone is not treated as an audit result; the parent owns exact-source and complete-package verification.

| Source | SHA-256 |
|---|---|
| `SourceMarkedPivotFullRange.lean` | `dfcd7b86dd15da7a60b511dfcd4ca59846e6a3867bb746c8b16c75f105c645fc` |
| `AdmissiblePivotSlabs.lean` | `3360ffcde27905cd41fc14f4b3fcadb6d8d949a6898b2a355a514a99e0390b72` |
| `AllAnglePivot.lean` | `442d13e8f9a331edcc59532bfa61f1028c9eddf9186d2530b88cdb128c8a5cf4` |
| `TwoEndsPivot.lean` | `f1139b640f719dda2828060ee80a2a3b8cb43e7889b9105ba6689fa22f8ff24e` |
| `TwoEndsGlobalization.lean` | `fca72eb28ade95cc8b17912eb5fee7a7637efcc765aaf6ed75476c51557f69b2` |
| `SpatialAssignment.lean` | `a48e66e0e3a1b57a6cf1be1e4bc12640ee8fe6d36db2062977ac3f4a942f00a9` |
| `MeasurableAngularPieces.lean` | `4cd58e215019596dbc061c8fed1056d23a75afd8d35ac0522ff55474abfe8e4f` |
| `MeasurableSeedDensityLengths.lean` | `2005fa25b02fbaa8d99e9cf70b39b616df178b4bf95f535186a0bf952a3b0f88` |
| `SamplingLengthRealization.lean` | `1732e22b425ac9321b2fc8edbbdd9eec6a06d27df0afb9997fecbc28409cfaa6` |
| `ProjectionConclusion.lean` | `db6e3a985bab44768929d9863c581a7ec8755713b9aea753a0fe7cee67cc62bb` |
| `AppendixEndpoints.lean` | `287a5eef6ceb74dce60587b2d13ce1d4876841a9e8f24a73dc0a7bc958c2e75e` |

This inventory makes no percentage-completeness claim and no inference from declaration counts. Further adapters being developed after these hashes must be assessed by their actual statements before these boundaries are removed.
