# Actual density and broadness recovery

`DensityBroadnessRecovery.lean` has 15 theorems and compiles cleanly. The final `recover` theorem and geometric inheritance use only Lean's standard `propext`, `Classical.choice`, and `Quot.sound` axioms.

Starting with actual original tube shadings F and arbitrary actual output subsets O, assuming `δ #F_i ≤ 2λ` and `δ Σ#O_i ≥ η λ M`, the module constructs the precise threshold set of tubes `δ #O_i ≥ ηλ/2`, an injective indexing e, and the actual full selected family G. It proves `N ≥ ηM/4`, full selected incidence at least `ηλM/2`, and per-tube normalized cardinalities between `ηλ/2` and `2λ`.

It then constructs a finite marked cell filter using the actual original and selected multiplicities: a cell is marked when the good multiplicity is at least `(η/8)` times the original output multiplicity. Exact double counting and actual finite row/reindex identities prove that at least half of the full selected incidence is marked. Marked incidence is exactly `Σ_i #(G_i ∩ Z)`, and every marked cell belongs to the selected full union.

On marked cells, actual projective cap broadness transfers from the original output with constant `K·8/η`. Full selected shadings inherit the original finite physical-ball two-ends bound with constant `B·4/η`. The full selected shadings are kept separately from their marked subsets; no per-tube marked density is claimed or needed. Admissibility, separation, boundedness and real cap bounds are inherited by a separate actual injective restriction theorem.

The construction permits empty original/output shadings and M=0. If a downstream theorem requires a nonempty index type, M>0 and `N ≥ ηM/4` yield N>0. No η≤1 hypothesis is silently imposed. Physical half-open-cell realization, width normalization, and the final hairbrush estimate are downstream verified interfaces rather than assumptions hidden in this module.
