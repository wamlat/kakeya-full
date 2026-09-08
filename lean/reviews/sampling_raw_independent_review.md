# Independent review: full-range raw sampling

**No substantive mathematical statement or linkage defect found.** Reviewed the complete final sources of SamplingParameterRange, SamplingRawMeans, SamplingRawAssembly and SamplingRawRealization against combined §6, Lemma 6.1 and (6.1)–(6.17), especially extracted lines 1322–1480. Also checked the actual Input/raw definitions, sharper probability assembly, cap-test transfer, SampleGood, and arbitrary-ball realization dependencies. This was read-only; no frozen source was changed.

## Actual probabilities and expectation linkage

The imported `SamplingNormalizedMeans.Input` is only the physical input record. The new path uses its `rawFull` and `rawMarked` definitions throughout, which are the actual intersection volumes divided by delta^ambient, on the finite positive-full support. It never uses row equalization. Nested measurable marked/full sets give 0≤q≤p≤1; every marked positive intersection belongs to the full support, so `marked_mean_eq` preserves the literal Wg exactly. The full expectation bounds retain original c0,C0.

The probability theorem constructs one outcome from the original coupled product law: at each pair the state probabilities are 1−p, p−q, q, the exact joint law induced by a shared uniform threshold. Independence is across distinct tube-cell pairs. The auxiliary factor 3/25 in `sharpBudget_eq_rescaled` is only an arithmetic identity converting the rate denominator 12 to 100; it is never substituted into the actual law or marked array. The constructed positive-mass outcome supplies full/marked positive support even when some probabilities vanish.

## Uniform threshold and geometry

The inequalities N^(1−s)≤lambda*N and N^(1−s−alpha)≤B*r^alpha*lambda*N use exactly r≥1/N, B≥1 and alpha≥0. Positive gaps s<1 and alpha<1−s are fixed before the uniform cutoff. Full failure has rate exp(−cf*N^(1−s)/100), ball failure exp(−cb*N^(1−s−alpha)/4); the polynomial test counts and high/cap rate with a0=64*(ambient+4) are sufficient. No equality-at-endpoint gap or specialized 1/3,1/4 restriction survives.

The geometric assembly derives the finite support, all ball-test counts, tube population from actual separated directions and bounded carriers, and cap tests centered at the original directions. Every arbitrary nonempty theta cap fits a 2theta test centered at an occupied row member. Thus only M cap tests are needed; no angular-net cardinality oracle is assumed. The literal theta=min(1/100,(1000K)^(-1/beta)/2), its log lower bound and delta≤2theta are derived from the fixed upper-log K budget. The cutoff precedes the actual family, shadings, lambda, xi, B and K. The stronger theorem needs no upper-log B or inverse-log xi budget: B≥1 suffices for concentration, and the deterministic low/high test handles small marked mass.

Ball means use only original full two ends on [delta,1]; enlarged balls above one use total full mass. The realized arbitrary-ball bound compares each cutoff to the same actual row mean, then to its actual full count. This avoids c0/C0 in the dimension-only two-ends factor 8*ballCoefficient=32*(1+ambient/2). The parameter range implies alpha<1, which justifies the fixed bound on 4^alpha and the cell-enlargement power.

## Exact output and source scope

Low cells have positive marked expectation strictly below the threshold, carry at least Wg/2, and have cardinality at least Wg/(2 threshold). The high output has full counts in [c0*lambda/(2delta),2*C0*lambda/delta], and preserves the sharper 2/3..4/3 actual-mean band. It proves both inequalities in (6.9), separately: sum marks≥Wg/4 and Wg/4≥xi/(8C0)*sum full. These use original Wg and original C0.

The same output stores one actual omega. Its full family has exactly the original indices/axes, so separation, boundedness and any optional cap condition are inherited unchanged. Only marks are restricted to high cells; no full incidences are deleted by that high-cell operation. The arbitrary-cell angular conclusion is relative to the actual marked row and holds with coefficient one tenth. Positive original intersections, width+ambient/2 center admissibility, and the explicit longitudinal mesh-interval grid bound are proved. The whole-cell union is contained in the **available cell union**, not the original measurable shading union; this matches source (6.11).

The remaining exact convention distinction stated in the author's report is real and correctly disclosed: these four modules use unit axes, fixed-width carriers, fixed bounded bases and separation delta. A wrapper for every comparable-length/fixed-multiple-separation convention of the manuscript is separate. Likewise the output uses open projective chord caps; the input marked broadness and optional real cap predicate have their explicit closed tests. There is no remaining probability, expectation, full-range parameter, marked-mass or support gap within these concrete conventions. This review makes no claim about the separate convention adapters currently under construction.

## Verification evidence

Verified exact current SHA against each existing audit JSON, exact full-source prefix in the corresponding audit file, all 30 named source theorem coverage, total 59 theorem and 77 declaration entries, no diagnostics/missing/custom axioms, and every collected axiom in {propext, Classical.choice, Quot.sound}. Independently recompiled SamplingRawRealization from its final source with zero diagnostics. No new audit of the entire imported project was claimed.

| Module | SHA-256 |
|---|---|
| SamplingParameterRange | `a09a111e233611842b818cf3a64eb5ffcf48e4f4c2ad03dbe1fb9e7f734baaaf` |
| SamplingRawMeans | `e5c70eec05a610febc7c9061d869058b6669adf691706107fbd256e56bb46192` |
| SamplingRawAssembly | `69396b3b26be6160d67cfd1365f222a8b61360497b1dec55ed192c1a286560bc` |
| SamplingRawRealization | `29ed1a394dbe384b5b34340c0d6a6e4d57d74264bc3fb785d25f87159d555b03` |
