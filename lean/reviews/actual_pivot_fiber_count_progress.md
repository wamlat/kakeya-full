# Actual pivot output count at one intermediate label

`ActualPivotFiberCount.lean` is complete, clean-compiled, built, and frozen: two theorems, no definitions. Both theorem audits use only `propext`, `Classical.choice`, and `Quot.sound`.

Main interface:

`ActualPivotFiberCount.output_count_at_intermediate S a z hδ hδ1 hkappa hwidth hadm`

For the actual `SampleSystem S`, actual marked angle `a`, and original intermediate grid label `z`, this proves

`card (((S.samples a).image (LegalSampleOutputs.output S a ...)).filter (fun f => f.2=z)) ≤ 4*PivotOutputCount.boxConstant n (n/2)*(1+2*width)/δ`

as a real cardinality bound in ambient dimension n. Inputs are 0<δ≤1, κ>0, width≥0, and the actual family admissibility. No total-output bound, sample-count premise, or cardinality premise is assumed.

If z belongs to the actual intermediate-label set, the proof takes its actual subtype index, identifies every encoded sample with that index using equality of the unchanged original intermediate labels, and maps each output injectively to its pivot label. Those pivot labels belong to the genuine `pairSet` for this exact index. `PivotOutputCount.pivot_output_count` supplies the normalized bound at mesh δ/(1+2width), and the final scalar identity gives the displayed physical constant. If z is absent, the output fiber is proved empty.

`restricted_output_count` gives the same bound for any finite restriction of the actual outputs whose intermediate coordinate equals z; its premises are literal subset membership and fixed coordinate, not a count estimate. This is ready for the finite collision-row restriction.

This proves the C*N pivot factor for a fixed i₀ in the paragraph following (5.17), physical PDF page 20. There is no intermediate-population factor and no union across different angle-specific pair sets.
