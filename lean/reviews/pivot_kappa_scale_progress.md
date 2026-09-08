# Uniform pivot scale closure

`PivotKappaScale.lean` is complete, compiled, and frozen: four theorems; every theorem's printed axiom set is exactly the permitted standard set (`propext`, `Classical.choice`, `Quot.sound`). No new axioms or placeholders were introduced.

`normalized_choice_cutoff` chooses a single `N₀ ≥ 1` from fixed `width, B₀, K₀, α, β, b, q, R, T` with α, β, R, B₀, K₀ positive and b,q,width nonnegative. For every later N ≥ N₀ and every positive B,K obeying B ≤ B₀ log(2N)^b and K ≤ K₀ log(2N)^q, the same explicit κ from PivotKappa satisfies

- 1/N ≤ κ/R;
- T ≤ N(κ/R)^20.

The cutoff is independent of N, the later B,K, density, tube count, directions, and shadings. This closes rather than assumes the manuscript's strong small-scale condition `N κ^20 ≥ C`. `choice_cutoff` is the unnormalized R=1 specialization. `normalized_choice_small_scales` returns an actual fixed δ₀ in (0,1] before δ,B,K, with the corresponding two conclusions for every δ≤δ₀ and budgets involving log(2/δ). It can feed `DiscreteEstimate.of_small_scales` directly.

The proof first uses the already proved inverse-log bound with exponent 1/40 to obtain κ/R ≥ a N^(-1/40), where a>0 is fixed. Exact real-power algebra gives N(a N^(-1/40)) = a N^(39/40) and N(a N^(-1/40))^20 = a^20 N^(1/2). Mathlib's proved divergence of positive real powers supplies their uniform common cutoff. This is an existential, fully proved cutoff; the file does not claim a simplified numerical formula for it.

The concentration tests remain in the frozen `PivotKappa.admissible`; combining them requires B,K≥1 as stated there. The small-scale theorem itself needs only positive B,K.
