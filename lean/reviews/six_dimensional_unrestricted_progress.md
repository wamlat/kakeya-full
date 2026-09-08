# The actual six-dimensional unrestricted shading estimate

`SixDimensionalUnrestricted.lean` is frozen and clean-built. Its eight proved theorems establish:

- `discrete`: DiscreteEstimate(6,5,33/8,33/8), uniformly over all actual finite shaded configurations;
- `measurable`: MeasurableEstimate(6,5,33/8,33/8), for arbitrary measurable shadings of relative density at least λ;
- `measurable_volume`: the exact sum-of-actual-tube-volumes formulation;
- `bounded_maximal`: the cap-free maximal-shading estimate in each fixed bounded position normalization;
- the first-step implications from exponent4 to33/8 in the corresponding measurable, actual-volume, and cap-free bounded predicates;
- `volume_lower`: explicit δ^(15/8+epsilon) λ^(33/8) times the actual tube-volume sum, with the visible inverse cap coefficient of MeasurableConfiguration.

The discrete proof applies the actual TwoEndsGlobalization.remove_two_ends theorem to TwoEndsPivot.six_dimensional. Before globalization its set exponent is33/8 and density exponent15/4. The proved removal of two ends changes density exponent to max(33/8,15/4)=33/8, preserving the set exponent. Both pivot inputs are proved fractional seeds, so no published-result axiom is used. The conversion to measurable shadings is the existing proved occupancy-class construction, and the actual-volume adapter uses the proved tube-volume comparison.

The first-step implications are stronger than conditional uses of M6(4): their conclusions are already proved with the base and lifted seeds discharged. The proof explicitly names the unused base hypothesis rather than treating it as an oracle.

The cap-free bounded theorem uses MaximalShading.bounded_maximal_of_volume. It derives the full ambient cap bound from actual fixed direction separation and absorbs that fixed cap coefficient into the constant. It does not silently reuse an arbitrary input A.

## Precise position boundary

These theorems quantify every fixed positive separation and bounded-base normalization before the estimate constant. No angular, marked, sampling, two-ends, density-class, or localization premise remains. The literal arbitrary-position predicate MaximalShading.Estimate is deliberately separate. Its actual measurable spatial reduction is being proved in another module; this frozen module does not claim that step.

## Verification

```
lake env lean -o .lake/build/lib/lean/SixDimensionalUnrestricted.olean SixDimensionalUnrestricted.lean
lake env lean ../six_dimensional_unrestricted_axioms.lean
```

Both completed with zero diagnostics. The audit uses the exact full source plus the production collector over all local declarations. All8 named source theorems and8 environment declarations depend only on propext, Classical.choice, and Quot.sound. No custom axiom, sorry, admit, unsafe, or native_decide appears. Exact SHA256: `942105ec8c6b5c687be573d10899cbbb34f77f0b8765f2181112ac2b5c16a0ee`. Machine evidence: `six_dimensional_unrestricted_audit.json`, `six_dimensional_unrestricted_axioms.lean`, and `.log`.

An independent agent also reviewed the exact specialization and MaximalShading adapter, finding no defect; report: `six_dimensional_unrestricted_independent_review.md`. Toolchain: Lean4.33.1 and mathlib `0df444a360eaa60ab8c11dca51a86af692955474`.
