# Literal geometric conventions of source Lemma 6.1

The remaining comparable-length, fixed-multiple separation, and closed-cap conventions are now covered by actual kernel-checked theorems. The six new modules listed below are frozen and cleanly compiled. Their exact-source audits pass for54 named theorems,131 local theorem declarations, and163 all local declarations, with only `propext`, `Classical.choice`, and `Quot.sound`. Together with the four full-range raw modules this phase comprises84 named theorems in ten sources. No frozen source or common build/verifier file was changed.

## Final actual theorem

`SamplingLengthRealization.construct` chooses a positive scale threshold before every actual family, per-tube length, measurable shading, density, marked fraction, B, and K. Its fixed parameters are dimension, a width upper factor, a base bound, an axis-length upper bound L, a separation factor sep>0, c0, C0, beta, the logarithmic K coefficient/exponent, and the arbitrary fixed range

`0<s<1`, `0≤alpha<1-s`.

The physical input consists only of actual measurable data and conditions. Each original axis is represented by its base and unit direction together with an explicit per-tube length. `lengthCarrier T length width` is the literal set of points within width of `T.axisPoint t` for `0≤t≤length`. All original lengths are at most the fixed L. The source's additional fixed positive lower bound on length is unnecessary for sampling; thus all comparable-length source inputs are covered. Likewise only the upper width factor is used. Directions have the original sep*delta separation, with no thinning or relabelling.

The final theorem constructs the actual source low/high alternative with raw probabilities at the ORIGINAL mesh delta. It preserves the exact source angular choice

`theta=min(1/100,(1000*K)^(-1/beta)/2)`

and the uniform lower bound with K0 and log(2/delta)^(-logPower/beta). No normalization ratio is inserted in theta.

## Exact support, means, and finite tests

`SamplingBoundedSupport` constructs a literal finite set of all positive full-intersection cells from an actual physical bound. Its support membership is equivalent to existence of an original full shading with positive measure in that exact half-open cell. It proves exact full and marked mass identities and physical ball expectations at the original mesh. No finite support/count or expectation oracle is supplied.

`SamplingLengthInput` derives the needed point bound from the original variable-length carriers and bounded bases, with fixed radius `max(0,R)+max(0,L)+width+1`. It also derives finite measure, actual nested probabilities, literal c0/C0 full means, exact original Wg, and all ball/cap expectation inequalities. Physical two ends is used only between delta and one; enlarged balls above one use total mass. The unchanged angular hypotheses are integrated directly over the original cells.

The actual separated-direction packing theorem at sep*delta gives `M≤packingConstant(n)*(1/sep)^n*(1/delta)^n` once delta≤1/sep. That extra fixed upper scale is included in the initial threshold. The physical support and ball test counts follow from the actual bounded grid geometry. The existing positive-gap union budget then constructs one coupled outcome for the raw p/q arrays.

Although `SamplingGeometry` separately proves exact common-homothety transport of grid membership and raw probabilities, the final sampling route does not transform any shading, mesh, or angle. The direct bounded-support proof avoids introducing a spurious new lower angular radius or a fixed K loss.

## Source outputs, on one unchanged outcome

The low alternative retains the exact original Wg: positive cells below the dimension-only threshold carry at least Wg/2, number at least Wg/(2 threshold), and therefore the stated xi*lambda*M/(2 delta threshold) lower bound.

For a high output, the following are proved for the actual shadings constructed from its single stored raw outcome:

- original tube indices, bases, unit directions, and the original physical parameter intervals `[0,length_i]`;
- `c0*lambda/(2*delta)≤#full_i≤2*C0*lambda/delta`, and additionally the sharper2/3..4/3 band around each raw mean;
- `sum #marks ≥ Wg/4 ≥ xi/(8*C0)*sum #full`, including the middle comparison separately;
- original-mesh full two ends at every physical radius in `[delta,1]`, with dimension-only factor `32*(1+ambient/2)` for alpha≤1;
- every selected center is within `(width+ambient/2)*delta` of an actual point on its ORIGINAL finite axis, without extending that original output interval;
- the fixed longitudinal-delta grid bound, original positive full/marked intersections, marks contained in full shadings, and full union cardinality at most the actual available support cardinality;
- selected whole-cell union contained in the available whole-cell union, as source(6.11) states; no false inclusion in the original measurable union is claimed;
- inherited original sep*delta separation and every optional cap bound with exactly the same coefficient and exponent.

The complete Output record contains the original arrays and one actual omega in `SampleGood`. The final construction proves this record exists. No random-outcome premise or desired geometric output is a caller hypothesis.

## Closed caps at exact theta

`SamplingClosedCaps` proves an actual unit-sphere fact: a closed chord cap of radius0<theta≤1 has squared diameter at most `4theta²-theta⁴`, hence diameter strictly less than2theta. Choosing signs of unit representatives transfers this to projective chord distance. An actual member of every nonempty closed theta-cap therefore centers one of the EXISTING open doubled tests containing the entire closed cap.

Consequently `SamplingLengthRealization.Output.closed_broadness` proves the one-tenth bound for CLOSED projective chord caps at the exact source theta, on the same outcome, without replacing theta or modifying the test mask/probabilities. All cap centers in this closed statement are unit vectors, as required for directions on projective space. The earlier raw report's open/closed limitation is superseded by this theorem.

## Scope and validation

This completes the raw, full-parameter, comparable-axis-length and fixed-separation-factor sampling construction in the package's precise Euclidean half-open-grid and projective-chord conventions. The source's upper-log B and lower-log xi conditions are not needed for existence beyond B≥1 and xi>0; only the upper-log K condition places the tested angular radius above the mesh. Hence the final theorem is stronger in those two conditioning ranges, rather than hiding their budgets.

The proof does not identify an angular metric with a different externally chosen convention without a comparison theorem. Its exact direction metric, closed tests, axis parameter intervals, width factors, and physical ball ranges are all visible. No source theorem is axiomatized.

Lean4.33.1 with mathlib commit `0df444a360eaa60ab8c11dca51a86af692955474`. Each source was built using `lake env lean -o .lake/build/lib/lean/MODULE.olean MODULE.lean` and audited by appending the production verifier's AUDIT command to its complete exact source. Diagnostics, all declared/local theorem dependencies, all local declaration dependencies, and source-theorem coverage were checked. Adjacent per-module JSON and logs provide exact counts and hashes.

| Module | Named theorems | Local theorem declarations | All local declarations | SHA256 |
|---|---:|---:|---:|---|
| SamplingClosedCaps | 6 | 8 | 8 | `e0601e7655fb29cd4069c6c2c1649cb05564d6f61879db20f241ec1d410e3d03` |
| SamplingGeometry | 7 | 14 | 15 | `726dde39fb3915ff83e1b9991e2e4d5ffd33747d72d019285190e4609ef06e0a` |
| SamplingBoundedSupport | 8 | 11 | 13 | `b1313fee65ab09892edfcfec27b6dd3961199ef348e4427901afe93e4ad0e56c` |
| SamplingLengthInput | 10 | 49 | 58 | `2aa8f1437ee876da5a3ab444af27e89a77703bc78234b66d039fb0dc7c92c0e4` |
| SamplingLengthAssembly | 2 | 11 | 15 | `7c1955db5eafd5d0939865afd50c938c1e971a07eb71babf7970d56fb82ef3cc` |
| SamplingLengthRealization | 21 | 38 | 54 | `1732e22b425ac9321b2fc8edbbdd9eec6a06d27df0afb9997fecbc28409cfaa6` |
