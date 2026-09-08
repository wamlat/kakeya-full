# Geometric output and fiber bounds: completed bounded phase

`formalization/PivotOutputCount.lean` derives the output-count and fiber-size estimates in combined PDF §5.3. It imports the existing actual grid geometry and `PivotWitnesses` legal endpoint records; it does not assume either desired count or a longitudinal-label packing bound.

## Actual sample model

`LabeledPair a delta width firstCoord secondCoord` stores two actual endpoint cell labels, deterministic projection-coordinate maps, the normalized legal endpoint inequalities, and actual center-to-shifted-axis distance bounds. From it, `LabeledPair.endpoints` constructs an existing `PivotWitnesses.Endpoints a` record. The pivot output is the actual half-open grid label `GridCells.label delta endpoints.pivot`.

Only the two endpoint labels are data fields. All remaining record fields are propositions. `LabeledPair.labels_injective` proves that one endpoint-label pair gives at most one sample; no multiplicity of proof witnesses or different projections is silently counted. The coordinate maps are fixed before sample selection, so a fixed first endpoint label fixes its coordinate exactly.

The intermediate label is retained in the dependent sample type. The full original sample set is the actual finite dependent union `I.sigma S`, where `I` is a finite set of intermediate labels and `S i` is a finite set of labeled endpoint pairs at that intermediate. `sample_labels_injective` proves injectivity into intermediate/first/second label triples. `sampleOutput` returns the actual pair `(rounded pivot, intermediate index)`.

## Uniform explicit bounds

Write

`box(k,w) = (2 ceil(w+1)+3)^k`,

`fiberConstant(k,w) = 3(2k+4) box(k,w)^2`.

For `0 < delta ≤ 1` and `0 < kappa ≤ 1`, the principal results are:

- `pivot_output_count`: for one fixed intermediate label, at most `4 box(k,k/2)/delta` distinct rounded pivots;
- `all_output_count`: at most `4 box(k,k/2) |I|/delta` complete outputs;
- `all_output_count_of_subset`: if intermediate labels are in the original first shading, replace `|I|` by that shading's cardinality;
- `pivot_fiber_count`: at most `fiberConstant(k,width)/(kappa delta)` distinct endpoint pairs at a fixed intermediate and rounded pivot;
- `all_output_fiber_count`: the same bound for every complete output fiber of the actual dependent sample set;
- `integer_output_fiber_bound`: the actual integer budget `ceil(fiberConstant(k,width)/(kappa delta))`, ready for `AngleFiberSelection`'s dyadic bound.

These constants depend only on dimension and the fixed physical projection width. The pivot-output constant is independent of kappa and projection width. No stronger scale relation such as `delta << kappa^20` is needed for these counts.

## How the geometric bounds are obtained

1. The legal pivot coefficient `c(1-a0/b)` is proved to have magnitude at most one. Thus, with the intermediate fixed, all exact pivots lie on a second-axis segment of length two. Actual grid rounding costs at most `k delta/2`, and the existing segment-grid theorem gives the stated `C/delta` output count.
2. First endpoint labels lie within `width delta` of a genuine unit first-axis segment, so their count is at most `3 box(k,width)/delta`.
3. Two samples with the same rounded pivot have coefficient difference at most `k delta`, proved from actual half-open cell rounding and the unit second direction.
4. For a fixed first endpoint, the legal inequality `1-a0/b ≥ kappa` gives a second-coordinate gap at most `k delta/kappa`. The actual second endpoint labels therefore lie near a physical interval of length `O(delta/kappa)`. The segment-grid theorem yields at most `(2k+4) box(k,width)/kappa` second labels. This is a linear inverse-kappa estimate; no ambient ball bound introducing `kappa^(-k)` is used.
5. Label injectivity and exact finite fiber sums combine the first/second counts. `output_fiber_card` additionally proves that a complete output fixes precisely one intermediate index, yielding its exact original endpoint fiber (or zero if the index is absent).

The general `interval_grid_count` also proves the actual grid bound `box(k,width) [(b-a)/delta+2]` for every positive-length longitudinal interval. Thus the manuscript's bounded number of occupied labels per mesh interval is derived from physical grid geometry.

## Scope and interfaces

The normalized legal endpoint inequalities and actual projection closeness are explicit geometric inputs in `LabeledPair`; they are not replaced by desired count assumptions. Root's `LegalAngleSamples`, `LegalTubeSamples` and `LegalSampleNormalization` modules construct those inputs from actual original tube shadings, two ends, one fixed projection map and a common spatial homothety. This module does not duplicate that construction or claim sample abundance.

No pair-selection or collision conclusion is assumed. The present bounds provide the geometric output-count and integer fiber-size inputs that were explicit hypotheses in `AngleFiberSelection`. The most-frequent second-tube packing bound and collision-energy estimate remain different geometric tasks.

The normalization here is exactly the existing `PivotWitnesses` one: the first endpoint coordinate is at most one and the second endpoint coordinate has magnitude at most one. A larger raw physical length bound must be passed through the common normalization bridge; it must not be silently treated as one.

## Verification

Lean 4.33.1 compilation and `.olean` generation pass, with no warnings. The nine principal theorem axiom reports contain only standard Lean axioms (`propext`, `Classical.choice`, `Quot.sound`), and the source has no `sorry`, `admit` or custom axiom. Compiler output: `audit_work/pivot_output_compile.log`.
