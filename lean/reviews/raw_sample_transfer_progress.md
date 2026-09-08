# Raw sample count transfer: completed bounded phase

`formalization/RawSampleTransfer.lean` contains eight proved theorems and one definition. It transfers the actual geometric bounds of `PivotOutputCount` to arbitrary finite original sample sets, with the same global output type `Cell k × Cell k` across angles.

The inputs are an actual finite raw sample set `P`, an output function on the raw sample type, an encoding of the valid-sample subtype `↥P` into dependent normalized `LabeledPair` records, and membership of every encoded sample in the actual finite record set `I.sigma S`. The output agreement is required only on valid raw samples. An injective map `indexLabel : Index → Cell k` forgets an intermediate subtype or proof wrapper. Fiber transfer additionally requires that the record encoding is injective. The output-support transfer does not need either injectivity hypothesis.

The three main interfaces are:

- `raw_geometric_output_count`: `#(P.image out) ≤ 4 box(k,k/2) #I / delta`;
- `raw_geometric_fiber_count`: `#(P.filter (out = f)) ≤ fiberConstant(k,width)/(kappa delta)` for every global cell-pair output `f`;
- `raw_integer_fiber_bound`: the same actual raw fiber is bounded by the ceiling of that geometric real bound.

Here the constants are exactly those already proved in `PivotOutputCount`; no additional factor appears. All geometric output and fiber bounds are invoked from their proved theorems, not supplied as new premises.

The finite proof explicitly identifies attached valid-sample filter cardinalities with the original raw filter cardinalities. For a nonempty raw output fiber, one sample determines a normalized output; injectivity of the forgotten intermediate coordinate forces every other sample in that raw fiber to have that same normalized output. The injective encoding then bounds its cardinality by that one actual normalized fiber. Empty raw fibers are handled separately and do not require a chosen index.

The precise encoding agreement is `out p.val = ((encode p).2.pivotLabel, indexLabel (encode p).1)`. It supports `Index` being a subtype of original cell labels with `indexLabel = Subtype.val`, as in root's `LegalLabeledSamples` adapter. There is no assumption that raw outputs are injective, no averaging over angles and no multiplicity factor from proof wrappers.

Compilation and `.olean` generation pass with no warnings. Six main theorem axiom reports contain only `propext`, `Classical.choice` and `Quot.sound`. No `sorry`, `admit` or custom axiom is present. Compiler output: `audit_work/raw_sample_transfer_compile.log`.
