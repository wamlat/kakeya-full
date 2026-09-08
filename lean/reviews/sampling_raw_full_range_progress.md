# Full-range raw sampling: source Lemma 6.1

All four new modules are frozen, compile without diagnostics, and pass exact-source audits. They prove 30 named theorems, with 59 local theorem declarations and 77 local declarations in total (including generated declarations). Every collected axiom is one of `propext`, `Classical.choice`, and `Quot.sound`. There are no custom axioms, `sorry`, `admit`, `unsafe`, or `native_decide` declarations. No existing frozen source, lakefile, verifier, registry, or published package was edited.

## Parameter range and uniformity

`SamplingParameterRange.source_mean_powers` derives the exact mean powers

- full rows: `N^(1-s) ≤ lambda*N`;
- ball cutoffs: `N^(1-s-alpha) ≤ B*r^alpha*lambda*N`, for `r≥1/N` and `B≥1`.

`uniform_source_budget` proves the complete polynomial/logarithmic union budget is below one at all sufficiently large N when `s<1` and `alpha<1-s`. The sharp full-row term uses the actual rate `exp(-cf*N^(1-s)/100)`, and the ball term has rate `exp(-cb*N^(1-s-alpha)/4)`. The high/cap contribution uses the dimension-only coefficient `64*(ambient+4)` times `log(2N)`. `source_sampling_narrow` then constructs one actual coupled outcome for the original nested arrays, with no failure-budget premise, in the full fixed range `0<s<1`, `0≤alpha<1-s`. This includes every positive alpha allowed by the manuscript and also its alpha=0 boundary.

The scale threshold is selected before the finite index types, arrays, and testing data. In the geometric assembly it is selected before delta, the original tube family, measurable shadings, lambda, xi, B, and K. Only fixed dimension, width, bounded region, density constants, s, alpha, beta, and the fixed logarithmic K budget enter its construction.

## Actual raw geometry and probabilities

`SamplingRawMeans` reuses the actual geometric `SamplingNormalizedMeans.Input` record; despite that existing namespace, the record contains only physical tube/shading hypotheses. These new modules use `rawFull` and `rawMarked` exclusively. They are exactly the original probabilities `volume(Full_i∩cell)/delta^ambient` and `volume(G_i∩cell)/delta^ambient`, on the actual finite support of positive full intersections.

The following are derived from physical data, not supplied as expectations or desired conclusions:

- `c0*lambda/delta ≤ fullMean_i ≤ C0*lambda/delta`, with the original c0 and C0;
- the exact marked identity `sum markedMean = Wg = sum volume(G_i)/delta^ambient`;
- nested probabilities `0≤q≤p≤1`, original positive-support geometry, all finite ball counts and original separated-direction counts;
- all tested full two-ends means from the original physical two-ends assumption only on `[delta,1]`; enlarged balls above one use total mass;
- all angular means from integrating the original almost-everywhere marked broadness;
- the literal angular scale `theta=min(1/100,(1000*K)^(-1/beta)/2)` and its uniform lower bound `choice(K0,beta)*log(2/delta)^(-logPower/beta)`.

There is no row equalization, no loss by `C0/min(c0,1)`, and no replacement of K by that ratio times K. The actual cap tests are centered at the original directions, so their count is bounded by M; a separate angular-net construction is unnecessary. The dimension-only high coefficient still covers the resulting polynomial number of tests.

## Literal low/high output

`SamplingRawAssembly.construct` proves the actual geometric alternative. `SamplingRawRealization.construct` returns the same alternative with the actual high outcome stored in an `Output` record. Its `good` field concerns exactly the raw arrays, actual cell subtype, actual ball/cap masks, and that one `omega`; it is proved by construction, never requested as an input.

The low alternative has the exact source guarantees: the positive cells below the threshold carry at least Wg/2, their number is at least Wg/(2 threshold), and hence at least `xi*lambda*M/(2*delta*threshold)`.

For a high output, the proved `Output` theorems give:

- unchanged tube indices and axes, inherited separation, bounded bases, and every optional real cap bound with the same coefficient and exponent;
- `c0*lambda/(2*delta) ≤ #full_i ≤ 2*C0*lambda/delta`; the outcome also retains the stronger `2/3..4/3` band around its actual raw full mean;
- `sum #marks ≥ Wg/4 ≥ xi/(8*C0)*sum #full`, including the middle inequality as a separate theorem;
- full two ends at every physical radius in `[delta,1]`, with the dimension-only factor `8*ballCoefficient(n)=32*(1+ambient/2)` for alpha≤1 (which follows from the parameter range);
- at each marked cell, every open projective cap of radius theta contains at most one tenth of the marked directions;
- all selected centers are in the width `width+ambient/2` enlargement of the original axes, and every longitudinal delta interval has the explicit grid bound `(2*ceil(width+ambient/2+1)+3)^ambient`;
- original positive full/marked intersection support, marked subsets of full shadings, selected union cardinality at most the original support cardinality, and inclusion of the selected whole-cell union in the available whole-cell union.

The final inclusion is into the union of available cells, not into the original measurable union. This is the distinction made explicitly in source (6.11).

## Exact scope and remaining distinctions

This closes the previously missing arbitrary fixed `(s,alpha)` sampling range and raw-probability constants for the package's actual normalized geometric model: unit axes, fixed width factor, fixed bounded bases, and separation delta. Source Lemma 6.1 permits comparable axis lengths and a fixed multiple of delta separation; a literal wrapper for every such geometric convention would need the existing geometric normalization machinery. No new universal comparable-length convention is asserted here. The angular conclusion uses the package's open projective chord caps at theta; the input broadness and optional CapBound use their existing closed-cap tests. These exact conventions remain visible in the statements.

The source also imposes inverse-log xi and upper-log B budgets. This sampling existence theorem does not need them: xi>0 and B≥1 suffice once the actual marked mass and full two-ends assumptions hold. Only the upper-log K budget is needed to put the chosen angular test above the mesh. Thus no missing B or xi budget is being silently assumed. The separate row-equalized sampling path used in the already proved pivot/operator chain is unchanged.

## Verification

Lean 4.33.1; mathlib commit `0df444a360eaa60ab8c11dca51a86af692955474`.

For each module, clean compilation used `lake env lean -o .lake/build/lib/lean/MODULE.olean MODULE.lean`. Exact-source axiom audits appended the production verifier's `AUDIT` command to the complete source and ran `lake env lean ../STEM_axioms.lean`. They checked all local declarations, separate theorem counts, all named source theorem coverage, and absence of diagnostics and untrusted axioms. The adjacent `STEM_audit.json` and `STEM_axioms.log` files record results.

| Module | Named theorems | Local theorem declarations | All local declarations | SHA256 |
|---|---:|---:|---:|---|
| SamplingParameterRange | 4 | 4 | 4 | `a09a111e233611842b818cf3a64eb5ffcf48e4f4c2ad03dbe1fb9e7f734baaaf` |
| SamplingRawMeans | 5 | 12 | 12 | `e5c70eec05a610febc7c9061d869058b6669adf691706107fbd256e56bb46192` |
| SamplingRawAssembly | 1 | 8 | 10 | `69396b3b26be6160d67cfd1365f222a8b61360497b1dec55ed192c1a286560bc` |
| SamplingRawRealization | 20 | 35 | 51 | `29ed1a394dbe384b5b34340c0d6a6e4d57d74264bc3fb785d25f87159d555b03` |
