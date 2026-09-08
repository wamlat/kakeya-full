# Absolute-cap inputs and full inverse-cap consequences

Two new modules are frozen and clean-built, with no diagnostics and production `.olean` files ready. They use only existing actual finite geometry and standard foundations. No frozen source or registry was edited.

## Precise weaker input

`AbsoluteDiscreteEstimate n m d p` quantifies a fixed geometric normalization and cap ceiling Q≥1 before the positive scale loss, estimate constant and every actual ShadedConfiguration. It requires only F.A≤Q and concludes c*delta^(m-d+eps)*lambda^p*M≤#actualunion, with no inverse-A factor in the input estimate. Thus the constant may depend arbitrarily on Q; uniform inverse-cap control is not hidden in the premise.

`AbsoluteTwoEndsDiscreteEstimate` is analogous, with the literal finite full-shading ball-count predicate. Q, geometry, B≥1, alpha>0 and eps>0 precede the actual configurations. These definitions reflect the source's absolute-cap analytic inputs, within the package's concrete all-scale normalized configuration conventions.

## Actual unchanged-scale selection

`AbsoluteCapReduction.construct` invokes `LocalizedDirectionThinning.thin_to_scale` at target=delta. The actual hierarchy/chart selection and fixed palette construct an injective original-index map and selected family, with whole original tubes and shadings. Its Selection record certifies:

- the SAME geometric normalization, delta and lambda;
- identical selected original tube axes and complete original shading rows;
- original separation, boundedness, admissibility and comparability;
- fixed coefficient Q=capConstant(k,m)≥1;
- selected population at least M/[retentionConstant(k,m)*A];
- selected union contained in the literal original union.

`Selection.full_two_ends` preserves exactly the original B and alpha since no cells on retained rows are changed. `Selection.transfer_bound` turns an actual selected-family estimate into the original bound with coefficient c/retentionConstant and exactly one original A^(-1). Empty families need no separate positive-population premise. The geometric thinning uses m≥0; no condition on the real set/density exponents is needed for this adapter.

The public `AbsoluteDiscreteEstimate.to_discrete` and `AbsoluteTwoEndsDiscreteEstimate.to_two_ends` select fixed Q before calling the analytic hypothesis and before seeing any original A, density, scale or configuration.

## Proposition8.1 full positive-density range

`AbsoluteCapGlobalization.lean` composes the actual absolute-cap adapter with the proved geometric two-ends removal. When C<1, normalized density lambda∈(0,1] permits weakening to exponent1. Since D≥1, max(D,1)=D=max(D,C), so this loses no desired final density power. The theorem consequently covers the whole source range1<D<m,C>0; its actual assumptions are slightly broader, m≥0 andD≥1.

`AbsoluteTwoEndsDiscreteEstimate.globalize` proves the full DiscreteEstimate with linear inverse-cap dependence and exponent max(D,C). `globalize_measurable` then uses the proved actual measurable conversion to give VolumeMeasurableEstimate, retaining original tube-volume normalization. No stronger full-A analytic assumption or population/support oracle is a caller premise.

## Scope and audit

This closes the analytic absolute-cap-vs-full-A input boundary in(5.4) and the weaker-input/C<1 boundary of Proposition8.1. It does NOT by itself normalize arbitrary fixed marked density multiples or c*delta separation in the finite marked pivot construction, nor does it identify a different angular-metric convention. A lifted cumulative-only input has a separate adapter under construction by root.

- `AbsoluteCapEstimates.lean`: SHA256 `bf72cdb76c3a9458b07494c69826db67f7c98dd2964a5950264b0172aa28ed88`; exact-source audit PASS8 named declarations (5theorems,2predicate definitions,1selection record), standard axioms only.
- `AbsoluteCapGlobalization.lean`: SHA256 `a031b3827a3b4bb415aedf6d18f4d6288b2b25cdc540d66a9cab8d5c1cd6f93b`; clean production build and exact-source audit PASS3 theorems, standard axioms only; evidence in adjacent full_source_audit files.

All audit source prefixes/final hashes are checked. The complete sources are compiled with appended axiom prints for every named declaration; no sorry/custom axiom or warning is introduced.
