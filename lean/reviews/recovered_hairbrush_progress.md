# Direct broad-grid hairbrush bound after retained-incidence output

`RecoveredHairbrush.lean` composes actual DensityBroadnessRecovery with the actual GridHairbrush theorem. It contains two theorems. The main `retained_output_hairbrush` constructs the selected tube family and marked cell set internally, applies the measurable geometric hairbrush through the verified exact grid realization, and concludes a lower bound for the original finite union cardinality.

Inputs are a nonempty actual tube family F, arbitrary finite output subsets O_i⊆F_i, original normalized upper density `δ #F_i≤2λ`, and total retained normalized incidence `δ Σ#O_i≥ηλM`. The original shadings have literal finite two-ends bounds; the output has literal pointwise Broad cap bounds. Direction separation, real cap bounds, the valid scale interval, and positive parameters are explicit. The theorem does not assume comparable output densities, a selected subfamily, marked mass, or a hairbrush inequality.

The recovery proves `η≤2` automatically from the mass and original upper bound. Thus the recovered lower density `ηλ/2` satisfies the kernel's normalization λ≤1 when original λ≤1, and the recovered B/K constants are at least one. Nonemptiness of the selected family follows from `N≥ηM/4`.

Let n=k+2 and W=widthFactor(n,width). The exact displayed final bound uses:

- full density `(ηλ/2)/W^n`;
- full upper density `(2λ)/W^n`;
- actual marked incidence at least `ηλM/(4δ)`;
- two-ends concentration constant `B'=(4B/η)(1+n/2)^alpha W^alpha`;
- angular concentration constant `K'=(8K/η)tau^(-beta)`;
- the actual kernel concentration radii and the explicit hairbrush logarithm.

Every η and W factor is retained in the statement. The left-hand expression is monotone in marked incidence; the proof substitutes its proved lower bound and uses the actual selected-union subset of the original union. No bounded-region assumption is introduced: a finite bound used only for generic cap-inheritance bookkeeping is constructed from the sum of the actual tube base norms.

The exported theorem is an actual broad-grid estimate for arbitrary retained outputs. Further simplification into monomial eta/tau powers or absorption of logarithmic losses is not asserted here. The surrounding decomposition, initial two-ends localization, and global lifted induction remain separate tasks.
