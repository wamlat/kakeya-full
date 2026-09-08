# Marked-compatible refinement inside actual angular reference unions

Three new modules are clean-built and frozen: MarkedDensityClass.lean, AngularRestrictedRefinement.lean, AngularRestrictedMeasurable.lean. Fresh source audits cover all 32 explicit declarations (12 + 6 + 14), including the Refinement structure and its population lower theorem. Every reported dependency is one of propext, Classical.choice or Quot.sound. No new external axiom is used, despite the separate authorization for published external inputs.

## Actual construction

CommonDensityLocalization was inspected but is not used blindly: it selects its density class by cardinality. Preserving marked incidence instead requires a full-density class selected with marked cardinality as the weight. MarkedDensityClass constructs that selection using weighted_dyadic_selection. If there are D+1 available classes, the selected class retains at least 1/(D+1) of the original marked incidence. It keeps whole full shadings of selected tubes.

The marked cell filter is literal: at a kept cell, original marked multiplicity must be at most 2(D+1) times the selected marked multiplicity. The exact finite incidence calculation shows that this removes at most half the selected marked incidence. Power broadness transfers with exactly the proportional factor 2(D+1); at every other cell the final marked row is empty. Broadness is never asserted to survive arbitrary thinning.

AngularRestrictedRefinement applies this construction to every actually kept angular group. It first uses DensityBroadnessRecovery on the actual group reference shadings, with original full shadings used only to derive the upper density and inherit two ends. The initial recovery retains sufficiently dense whole reference shadings and restores their marked broadness. The marked-weighted dyadic class then supplies exact comparable full density.

The output `Refinement P lam B alpha g` is proof-bearing, with an actual finite family, marks and an injective map into the original active group indices. For EVERY selected tube, its full shading equals the corresponding original P.family g shading. Thus its full union is in the exact old restricted reference union used by AngularPiecePopulation. The resulting full sets are not AngularSeedRealization.Full, which could be larger and lack the required overlap.

## Quantitative losses

Write eta=P.eta, Ng=#active(P.shading g), K0=4^beta*(4*angularConstant k). The constructed family has:

- common full density density in [eta*lam/2, 2*lam], with Comparable delta density;
- positive population N, and eta*Ng/[32(D+1)] <= N;
- D+1 <= log(4/eta)/log(2)+2;
- delta * total final marked incidence >= eta*lam*Ng/[8(D+1)];
- final marked incidence >= total final full incidence/[4(D+1)];
- marked power broadness coefficient (K0*8/eta)*2(D+1), on every actual marked row;
- full two-ends coefficient B*4/eta, derived from original full shadings;
- actual full and marked cell unions inside the original group reference union.

Here eta=3/[32*angularConstant(k)*(J+1)], and the already-proved depth bound is J <= log(1/delta)/log(2). Consequently the displayed losses have explicit logarithmic control; no unspecified class-count parameter remains. Each group selects its own density class, but all its densities have the common lower/upper bounds above and all class depths have the same displayed uniform bound. A global identical density class across groups is not asserted.

## Exact measurable realization

AngularRestrictedMeasurable uses the same existing width homothety W=widthFactor(k+1,width). For the exact selected index e(i), it proves:

    Full_i = AngularSeedRealization.Ref(P,width,g,e(i)).

Marks are literal normalized cell unions and lie in Full_i, hence in the same Ref_i. Both are measurable and finite. Original physical carriers contain the full sets; no transformed carrier membership is assumed. The actual physical density is density/W^(k+1), with full volume between that density times delta^k and twice that amount. The marked fraction is unchanged because the common volume factor cancels. Marked power broadness holds at every physical point by the exact inverse grid label, including half-open boundaries. The full two-ends coefficient is (B*4/eta)*(1+(k+1)/2)^alpha*W^alpha and the conclusion holds at every radius r>=delta, using the existing total-mass fallback above radius one.

## Exact remaining boundary

This closes the restricted-union issue BEFORE anisotropic unit-segment selection: both final full and marked sets stay in the original Ref unions whose overlap is proved. The subsequent anisotropic normalization must select unit segments in a way that preserves enough marked mass, and any further tube/density selection must again justify marked broadness through proportional multiplicity. That separate task is owned by geometry_audit. We do not claim that selecting the segment with greatest FULL mass preserves marks.

The finite density upper bound is explicitly 2*lam, not silently reduced to one. The measurable physical density is density/W^(k+1); if a downstream convention requires density<=1, a sufficiently large fixed common normalization or a documented equivalent parameter conversion is still needed. No independent tube translation or rescaling is used in this construction. Spatial-box localization and complete four-case Section 7 numerical assembly remain separate interfaces.

## Validation and dependencies

- MarkedDensityClass imports MarkedPruningRecovery and ScaleChoice.
- AngularRestrictedRefinement imports MarkedDensityClass and AngularPiecePopulation.
- AngularRestrictedMeasurable imports AngularRestrictedRefinement and GridMarked.
- Clean source builds: marked_density_class_compile.log, angular_restricted_refinement_compile.log, angular_restricted_measurable_compile.log.
- Fresh audits: restricted_marked_finite_full_source_audit.lean/.log (18 declarations); restricted_marked_measurable_full_source_audit.lean/.log (14 declarations).

SHA-256:
- MarkedDensityClass: 49dfa2108c50649617873e2a881ef111f1512fd0a4c2c11c91c5baef64c98c7f
- AngularRestrictedRefinement: 4d791425ec2590bf78fd85c7780ccd8b9e5d4ef7e8d774026d2aac12732a33fa
- AngularRestrictedMeasurable: 724c684005157a59bef87f5da6e69bbcf46b383b97e4019538b051c176395bf2
