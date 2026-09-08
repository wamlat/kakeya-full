# Independent scalar review of the literal Section 3.3 mass pruning

No substantive mathematical defect was found in the final frozen sources. I read both modules end-to-end against combined.txt lines464–538, including the exact same-data definitions and every mass inequality. This review is read-only; the parent owns compilation, axiom audits and integrated publication.

Final reviewed hashes:

- `SourceGoodMass.lean`: `cc8c4b79d7b9085960e8cfc8f33b7a4df86db50b21d28c29b46285496c7b3f27`
- `SourceDensityPruning.lean`: `8ba01cd9897ceee6de47c453913a6f95879da65ce566b07d7d031721db92b8af`

The good set is exactly {old multiplicity <= 2*surviving multiplicity}. At a bad point the surviving incidence is at most deleted incidence; at a good point bad-row incidence vanishes. The proof integrates these actual finite sums. All reference rows are measurable and finite where integral subtraction is invoked; all surviving and bad rows inherit finiteness by subset containment. No nonintegrable real-integral identity or infinity-minus-infinity operation is used.

The deletion threshold is exactly a*measure(Full_i)<=measure(Y_i), keeping equality and empty permitted rows. The actual survivors are Y_i or empty on the SAME original index. The deletion estimate is a pointwise scalar inequality summed over these actual masks. The assigned piece operation partitions every original index by one prescribed assignment; `piece_mass_sum` proves the exact equality with total original mass, so there is no loss depending on the number of pieces.

The parent mass theorem fixes a=kappa/8 and assumes the literal retained-mass budget kappa*I<=W. It constructs D<=W/8. Actual good mass is at least W-2D, hence 3W/4. Retained pieces are defined by goodMass>=survivingMass/2. Each rejected good mass is at most its bad surviving mass, so discarded good mass is at most D. This gives W-3D>=5W/8. None of these desired retention conclusions is supplied as a premise.

The full surviving shadings remain Y_i on retained original indices. The goodRows are separate marks on these full shadings; they do not replace the full rows used for density or two ends. The exact fractions therefore match source (3.5), (3.9) and (3.10), including equality cases. kappa=0 and empty input are covered by the arithmetic theorem, with vacuous or zero bounds as appropriate.

The generic mass theorem requires only finite measurable Y; Full enters its explicit real-mass budget and threshold. It does not assert Full is measurable/finite or Y_i subset Full_i, because those facts are not necessary for its own algebraic conclusion. To claim source (3.6)–(3.7), one must additionally supply actual finite full sets, original subset containment, and positive a, together with the original full density and ball inequalities. Those are explicit inputs to my separate SourceDensityPruningGeometry companion. It would be incorrect to infer two ends or preserved broadness merely from the mass theorem; the companion constructs those implications on the same masks/good sets.
