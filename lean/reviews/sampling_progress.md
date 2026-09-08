# Sampling probability phase: completed kernel-checked module

`audit_work/formalization/Sampling.lean` now compiles successfully with Lean 4.33.1 and the project's pinned Mathlib revision. All **50 exported theorems** were checked with `#print axioms`; all depend only on `propext`, `Classical.choice`, and `Quot.sound`. The final compile has no warnings, errors, `sorry`, custom axioms, or `native_decide`. The verification log is `audit_work/sampling_compile.log`.

## Actual probabilistic construction

The sample space is `ι → Fin 3`, where each finite index can represent a tube–cell pair. State 0 is absent, state 1 is full-only, and state 2 is marked. Given `0 ≤ q_i ≤ p_i ≤ 1`, the one-coordinate probabilities are exactly

- absent: `1−p_i`;
- full-only: `p_i−q_i`;
- marked: `q_i`.

Their product is proved nonnegative and normalized to one. `FiniteLaw.toPMF` converts the model into a genuine Mathlib probability mass function, and `probability_eq_sum_pmf` identifies event probabilities with sums of its masses. The arbitrary-function product-expectation factorization proves coordinate independence directly. Full and marked selection at a *single* coordinate are intentionally coupled, as in the PDF's shared-uniform construction.

Marked incidences form an actual finite subset of full incidences. The real-valued full/marked counts equal the cardinalities of those finite sets. Exact means, both for the whole configuration and arbitrary masked subsets, are proved from the constructed law.

## Concentration derived, not assumed

The one-coordinate and independent-product MGF identities are proved exactly. From `1+x ≤ exp(x)`, the module derives

`E exp(tX) ≤ exp(μ(exp(t)−1))`

for every real `t`, for actual full/marked counts and every finite subset mask on the *same product space*. Exponential Markov is proved from finite sums, giving Chernoff bounds. Consequences include:

- `(6.14)`: `Pr(X≤μ/2 or X≥2μ) ≤ 2 exp(−μ/12)`;
- `(6.15)–(6.16)` probabilistic input: if `u≥4μ`, `Pr(X≥u)≤exp(−u/4)`;
- `(6.18)` lower tail: `Pr(X≤μ/2)≤exp(−μ/8)`;
- `(6.18)` angular tail: if a cap count has mean `ν≤μ/1000`, then `Pr(Xcap≥μ/20)≤exp(−μ/8)`.

The angular upper bound is proved using exponential parameter `t=3` and the elementary verified bound `exp(3)≤26`, so no informal optimization or integer-threshold rounding is involved. Thresholds are real. `coupled_angular_failure` combines the actual marked cell/cap events without asserting that overlapping tests are independent.

## Simultaneous realization and support

`coupled_simultaneous_realization` handles an arbitrary finite family of full/marked subset tests on the common product space. Each test requests either a density band or a large upper threshold. Under the *explicit sum of the derived Chernoff expressions being below one*, it produces one outcome satisfying all tests. It does not assume individual failure probabilities as external inputs, or assume a simultaneous good event.

A strengthened finite-probability existence theorem obtains a **positive-probability outcome**. This matters: it implies no incidence with `p_i=0` is selected as full, and no incidence with `q_i=0` is marked. Those support properties are included in the simultaneous-realization conclusion. Thus the model respects the positive-measure support convention in Lemma 6.1.

## Remaining interface scope

The probability core is now machine proved. The finite geometry/application layer still needs to instantiate masks for tube, ball, cell, and direction-cap tests; derive their expectation inequalities from measurable shading assumptions; assemble the distinct test types into one event budget; deduce marked total-mass retention; and prove the asymptotic `N₀` bounds for the polynomial/logarithmic test counts. No ambient Euclidean geometry, actual measurable intersection integrals, geometric nets, or full statement of Lemma 6.1 is claimed here. `SamplingApplication.lean` is the next bounded phase for the finite assembly.
