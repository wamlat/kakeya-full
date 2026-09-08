# Original bounded-length marked normalization

All four modules, including the final `SourceMarkedLengths` original-family theorem, are frozen, clean-built and exact-source audited: 17 named source theorems, 56 local theorem declarations and 65 local declarations total, all standard-only. No diagnostics or forbidden constructs were found. No existing or frozen Lean module, lakefile, verifier, registry or delivered package was edited.

`MarkedLengthNormalization.normalizedFamily F W` uses the same integer full-shading labels and every same original tube index. Each axis base is divided by one common W, and every direction is exactly unchanged. A literal original axis segment of individual length ell_i<=W lies after this map inside the actual normalized unit carrier; no per-tube dilation or probabilistic row reweighting occurs. The common cell-center identity is proved exactly. The union of integer labels is literally unchanged.

`MarkedLengthInput.Input` contains only original scale/cap/density/mark/broadness/full-two-ends assumptions and actual membership of old cell centers in `SamplingGeometry.lengthCarrier` for the indicated individual lengths. `bounded_lengths` fixes W=max(1,lengthUpper), then proves an actual `MarkedGridNormalization.Input` with:

- delta_new=delta/W and lambda_new=lambda/W, so all original lower/upper row inequalities are unchanged;
- the exact same marks, marked incidence total, one-tenth cap fraction, theta and xi;
- original directions and smaller-mesh cap bound with unchanged real exponent m and coefficient A;
- fixed separation coefficient and width unchanged, normalized base bound R/W;
- full two ends with coefficient B*W, uniformly for every 0<=alpha<=1.

For the last item, every new ball pulls back to the original ball of radius W*r. The original condition applies whenever that radius is at most one; above one the total row count and B>=1,alpha>=0 give the estimate. The exact coefficient B*W^alpha is bounded by B*W since W>=1 and alpha<=1. Thus the fixed multiplier of B is independent of alpha and original scale. The same full/marked arrays and original occupied-cell count are preserved.

`MarkedLengthAlgebra.choice_identity` proves that choosing the source geometric coefficient with the full fixed product C_grid*W makes the concentration expression identical to the unit theorem's expression at B*W. The resulting original kappa is exactly the unit theorem's kappa divided by W. It is therefore no larger, with no extracted alpha-dependent constant. `rescaled_cutoff` proves that the original N*kappa^20 cutoff implies the actual finer-mesh cutoff.

The final source composition uses `SourceMarkedNormalization.source_fourth` with its literal N>=2-only absolute-cap base and paired-error cumulative lifted inputs. It changes the mesh and density together, weakens the actual kappa power using H>=0, and invokes the scalar `transport_fourth` with support-inflation parameter n=0 because this common dilation preserves integer union cardinality. This zero parameter is only an algebraic encoding of no additional union inflation; the actual direction exponent remains H=5(actualAmbient-1)+6q+12. All scale/density/log factors are fixed before original B,theta,alpha,delta,lambda,M,A and all axes/marks.

The source scope includes arbitrary fixed positive lower/upper density multiples, fixed positive separation, fixed width, fixed bounded positions, and individual axis lengths with a fixed upper bound. A positive lower axis-length bound is unnecessary for the stronger formulation and comparable lengths are included. Empty population remains omitted by the original marked input, matching the source's explicit convention. No modified family, broadness, energy or normalized output is assumed by the public adapter.

Validation uses Lean4.33.1 and pinned mathlib `0df444a360eaa60ab8c11dca51a86af692955474`. Exact source is recompiled with the production all-declaration AUDIT appended, and all local declarations are checked to use only propext, Classical.choice and Quot.sound. The aggregate record is `marked_length_complete_audit.json`; per-stage records are `marked_length_normalization_audit.json`, `marked_length_algebra_audit.json` and `source_marked_lengths_audit.json`. The parent owns the subsequent integrated build/audit/publication. An individual audit does not add these files to already frozen checkpoint20.

| Frozen module | Named source theorems | Local theorem declarations | All local declarations | SHA-256 |
|---|---:|---:|---:|---|
| MarkedLengthNormalization | 10 | 12 | 14 | 5ea82c09f6b8cf490214ba7289a622a61f1c4773be9606ebe7daa58ebd9ab861 |
| MarkedLengthInput | 2 | 31 | 37 | 3425378039d183f61a4ed092ca9530264e9f144cd9c4c450f3c7bd48c3d89066 |
| MarkedLengthAlgebra | 3 | 10 | 10 | 39a313f959f9424cf83c06284233f2f23ca3dd2469117c4491c0cc536021968c |
| SourceMarkedLengths | 2 | 3 | 4 | 9b7c8685193c4bb78e95523947f316b64840ffa7ba558f4bf7b5dbfe3c764e8e |

The final public `SourceMarkedLengths.source_notation` is the source E^4 inequality for the actual original occupied-cell union at N>=2, including the exact H, xi, log(2N), N, lambda and S=M/N^m powers. Its only analytic premises are `SourceAnalyticInputs.Base` and `.Lifted`; its only geometric/mark premises are the actual raw `MarkedLengthInput.Input` and the fixed length ceiling. The source cutoff T<=N*kappa^20 is original-scale. The fixed A0 inverse is absorbed in the fixed positive constant. The finite agent is independently reviewing the final four-module chain.

This report does not equate the unit-axis predicates for other unmarked estimates with a separately named variable-length theorem. Generic Prop7.1/8.1/endpoint length wrappers, and actual-variable-tube-volume maximal normalization, remain distinguishable API statements until explicitly composed. It also does not infer paper completeness from declaration counts.
