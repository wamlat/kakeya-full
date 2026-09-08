# Actual whole-label selection and exact fiber representatives

`ActualLabelSelection.lean` is complete, clean-compiled, built, and frozen: four theorems, one definition, and the proof-bearing `Selection` data structure. The separate audit checks the definition, structure, and all four theorems; every dependency uses only the standard foundational axioms.

`construct S hA hδ hδ1 hlam hkappa hkappa1 hwidth hadm hcomp hsep` returns a nonempty actual `Selection S hkappa hwidth hadm`. Its hypotheses are an actual legal SampleSystem on an actual finite tube family, nonempty actual marked-angle population, 0<δ≤1, λ>0, 0<κ≤1, width≥0, original admissibility/comparability, and original δ direction separation. There is no geometric label-count premise, no collision-count premise, and no extra small-scale condition: the proved per-output original-second-index count holds at all these scales.

The fixed integer label budget is

K = ceil(packingConstant(k) * [4(1+2width+(k+1)/2)(1+2width)/κ²]^k)

in ambient dimension k+1. It is proved positive and supplied to the finite theorem by `LegalOutputDirections.second_indices_integer_count`. The other budgets are the actual proved LegalSampleSelection sampleBudget, outputBudget, cutoff, and fiberBudget.

The constructed record exposes:

- actual source dyadic whole-edge set Ω and retained Ωstar, both nonempty and subsets of the original angle/output edge set;
- exactly unchanged output support after selecting a most-frequent original second-tube label at each output;
- whole-class retention, maximal class cardinality, and a constant original second index over each retained output;
- dyadic size h=2^level, its threshold and upper bounds, source sample/edge lower bounds, integer retention |Ω|≤K|Ωstar|, and real retained-edge lower bound;
- the derived Cauchy support bound conditional on a future bound for the actual collision energy;
- an injective enumeration of all retained outputs, one chosen incident angle for each, and exactly h original legal triples from that angle's own fiber, with the exact total mass hQ.

`Selection.retained_fiber_range` shows no surviving whole edge was shortened during label selection. `Selection.chosen_samples_actual` explicitly recovers original sample membership and the exact output for every selected triple. These help the subsequent collision-energy and lift constructions use the record directly.

The collision-energy bound itself remains a separate geometric assembly and is not asserted here.
