# Actual fixed-output second-tube count

`LegalOutputDirections.lean` is complete, clean-compiled, built, and frozen: 19 theorems and 3 definitions. `LegalOutputDirectionsAudit.lean` checks every declaration, including the proof-bearing `sampleFiber` constructor. No custom axioms or proof placeholders were added.

This closes the first geometric counting assertion in combined §5.4, physical PDF page 20, between (5.15) and (5.16). Let the ambient dimension be n=k+1, let R=1+2width, and set C(n,width)=1+2width+n/2. For an actual `LegalAngleSamples.SampleSystem` and its actual `LegalSampleOutputs.output`, the file constructs the finite set of distinct original second-tube indices occurring at one output f=(z₀,i₀). This is exactly the image of the original second index over `AngleFiberSelection.outputEdges`, so repeated angles or endpoint samples do not multiply the count.

Theorems proved:

- Every original sample constructs an actual normalized `PivotWitnesses.Fiber`. The pivot rounding field follows from deterministic half-open grid labels; the intermediate rounding field follows from the actual original tube incidence and shifted-axis projection. Neither is a caller-supplied geometric approximation premise.
- The legal coefficient has absolute value at least (κ/R)², by the already proved endpoint formula. The two observed normalized labels differ from that coefficient times the second direction by at most 2Cδ/R.
- Every represented original second direction lies within projective distance 4CRδ/κ² of `unitize(cellCenter δ z₀ - cellCenter δ i₀)`. Positive homothety invariance of this observed direction is proved explicitly.
- If the output is represented and 4CRδ≤κ², its observed displacement is nonzero and the displayed center has norm one. The nonzero condition is derived from the legal coefficient and actual rounding, not assumed.
- If the ORIGINAL family is δ-separated, the number of distinct original second indices at every output is at most `packingConstant(k) * (4CR/κ²)^k`, equivalently `packingConstant(k)*(4CR)^k / κ^(2k)`. This is the manuscript's κ^(-2(n−1)) loss, with fixed geometric constants and no δ, density, M, or A dependence.
- `second_indices_integer_count` provides the ceiling of that real bound, ready for the finite `AngleFiberSelection` label budget. It holds also for absent outputs and does not require the small-scale test: the geometric cap bound and projective packing themselves cover that case.
- `output_scale_of_twentieth_power` shows the existing strong condition `(1/δ)κ^20 ≥ 4CR` implies the explicit noncollapse test when κ≤1. Together with `PivotKappaScale`, this test has a single proved cutoff chosen before all configurations.

The exact named interfaces are `sample_output_cap`, `second_indices_cap`, `second_indices_displacement_ne_zero`, `second_indices_center_unit`, `second_indices_count`, `second_indices_integer_count`, and `second_indices_count_polynomial`.

The next geometric dependency is the collision shell estimate (5.17): actual competing first directions lie within Cδ/κ of the specific two-plane, with O(κ^{-(n−2)} Nφ) separated directions in each φ shell. The common first-tube intersection labels, pivot choices, and second-tube intersection labels must then be counted and summed for (5.18). This module does not assume or claim that later collision estimate.
