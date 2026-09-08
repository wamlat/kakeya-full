# Actual simultaneous selected-output line data

`SelectedOutputPairs.lean` and `SelectedOutputSlabs.lean` are complete, clean-compiled, built, and frozen. They contain 28 theorems, eight definitions and one proof-bearing structure (plus the original output-index abbreviation). All 37 named declarations passed fresh full-source axiom audits with exact source-prefix checks. There are no errors or warnings; the exact union of axioms is `propext`, `Classical.choice`, and `Quot.sound`.

The input is an actual `ActualLabelSelection.Selection S`, not an abstract family satisfying sample-count or pivot-count assumptions. Its original output type is retained unchanged, namely `Fin (outputSupport P.retained).card`.

`SelectedOutputPairs` derives actual membership of each chosen output's intermediate label in its chosen angle's intermediate set. It constructs the actual common normalized angle and a homogeneous LabeledPair encoding of every sample in exactly `P.chosen_samples q`. The encoding is injective and agrees with the earlier dependent actual encoding. Its finite image `raw P q` has cardinality exactly `2^P.level`, all pairs have pivot label `(P.chosen_output q).1`, and every pair decodes to its own original selected triple. A reference pair is chosen from this actual nonempty raw set. Original output injectivity gives injective intermediate labels at each fixed pivot.

All normalization parameters are literal in the types:

- original ambient dimension k+1; lifted dimension k+2;
- normalized mesh δ' = δ/(1+2width);
- normalized transverse parameter κ' = κ/(1+2width);
- actual projection width 2width.

`SelectedOutputSlabs.commonK` is exactly `SelectedFiberSlab.commonCount (k+1) (2width) κ' (2^P.level)`. It is positive and satisfies the explicit lower and upper nonempty-floor bounds, with lower bound `(κ')^6 2^level / [20 multiplicityConstant(k+1,2width)]`.

For every original output q, `LineData P q` records an actual chosen unit slab, exactly K selected lifted grid cells, containment in the actual raw lifted-cell image, center-defined slab membership, and an injective original endpoint-pair representative for each retained cell. `selectedLine` constructs all these records simultaneously as one function on the unchanged original index type. Its only additional hypotheses are 0<δ≤1, κ≤1, and the explicit normalized perturbation test `(k+1)δ' ≤ (κ')^5/4`. All nonemptiness, common-pivot and sample cardinality premises of the existing slab theorem are discharged.

The total selected-cell population equals exactly KQ. Representatives remain in the original selected sample fiber, and both original endpoint labels remain in their original full tube shadings. The original retained output type is explicitly proved nonempty. The normalized density δ'K has a fixed upper bound from actual geometric pivot-fiber counting.

The module also derives the geometric interfaces needed next: actual intermediate projection error at mesh δ', reference slope norm at most one, and pivot residual bounded by `[2width+(k+1)/2]δ'. Under bounded original tube bases, the normalized angle vertices lie in the fixed region `PrunedGraphLift.regionRadius width R`; no separate per-output translation or bounded-vertex assumption is introduced.

The remaining bridge is to group these actual LineData records by their actual pivot/slab pair, construct the actual normalized unit-tube families for every group, compute the common residue colors, and feed those families into the already proved actual grouped incidence/pruning construction. The original survivor-cell ball count must be transported using `PrunedScaleTransport` before it is used at mesh δ'.
