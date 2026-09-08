# Literal maximal-shading conclusions, including arbitrary positions

`MainMaximal.lean` is frozen and clean-built. Its nine theorem declarations compose the actual discrete, measurable, ambient-cap, and arbitrary-position spatial conversions to prove the manuscript's literal maximal-shading predicate.

`MaximalShading.Estimate n d` means: for each fixed positive projective direction-separation coefficient and each epsilon>0, a positive constant is chosen before every finite family of unit radius-δ tubes, all tube positions, every0<δ,λ≤1, and arbitrary measurable shadings Y(T)⊆T with volume(Y(T))≥λ volume(T). The conclusion is

`volume(union Y(T)) ≥ c δ^(n−d+epsilon) λ^d sum_T volume(T)`.

There is no cap coefficient, cap condition, or bounded-base premise in this predicate. The tube volumes are actual Euclidean Lebesgue volumes, not an assumed normalization. The source conventions are represented by radius-δ neighborhoods of unit segments and the proved unoriented projective chord distance.

The final theorems are:

- `endpoint` and `endpoint_formula`: every integer n≥6 with exact D_n=3+(2−sqrt2)(n−4);
- `six_first`: M6(33/8), with both analytic seeds already proved;
- `six_first_step`: the exact implication M6(4)→M6(33/8), in the same literal arbitrary-position measurable predicate (the conclusion is independently proved);
- `six_endpoint`: M6(7−2sqrt2);
- `eight_endpoint`: M8(11−4sqrt2);
- `six_diagonal_limit`: M6(29/7);
- `eight_diagonal_limit`: M8(37/7).

The two recorded diagonal limits use the proved simultaneous set/density weakening for actual integer shadings, then the actual occupancy conversion to arbitrary measurable shadings. They do not rely on incorrectly comparing density exponents alone.

The arbitrary-position step is the concrete `MaximalPositionReduction.bounded_to_unbounded` theorem. It assigns each original tube one actual unit spatial cell carrying a fixed fraction of its measurable shading. Every original tube remains once. Each spatial group is translated by one common origin to uniformly bounded bases. Actual tube and selected-union volumes are preserved, and disjoint OLD spatial cells supply the sum bound. The fixed retained density fraction is absorbed before all configuration data. Thus no unsupported varying-origin volume comparison or spatial-partition oracle remains.

## Verification and trust boundary

```
lake env lean -o .lake/build/lib/lean/MainMaximal.olean MainMaximal.lean
lake env lean ../main_maximal_axioms.lean
```

Compilation and the exact full-source environment audit returned zero diagnostics. All9 named source theorems depend only on propext, Classical.choice, and Quot.sound. No published-result axiom is used by these results; no custom axiom, sorry, admit, unsafe, or native_decide occurs in source. `main_maximal_audit.json` records the exact source hash and local environment counts. Full audit evidence is `main_maximal_axioms.lean` and `.log`.

These are kernel-checked statements about the formal predicates. The module does not by itself assert a separately formalized operator-norm or Hausdorff-dimension theorem, nor validate every informal proof sentence in the manuscript. The surrounding audit reports track the repaired or alternative constructions and statement fidelity. The full frozen-project rebuild and independent reviews are managed separately by the parent verification task.

Toolchain: Lean4.33.1; mathlib `0df444a360eaa60ab8c11dca51a86af692955474`.
