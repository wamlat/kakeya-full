# Actual measurable sampling assembly

`SamplingMeasurableAssembly.lean` is frozen and clean-built. Its full-source audit recompiles the exact source followed by all nine named declaration axiom reports. All depend only on `propext`, `Classical.choice`, and `Quot.sound`; there are no custom axioms or placeholders.

## Exact public result

`SamplingMeasurableAssembly.construct` fixes ambient dimension `n+1`, physical width and base bound, density constants `c₀,C₀`, broadness budget constants `K₀,beta,logPower`. It then chooses a positive `δ₀≤1` **before** the original family, measurable shadings, density, marked fraction, two-ends parameters, and outcome.

For an actual `SamplingNormalizedMeans.Input`, original `δ` separation, `δ≤δ₀`, `lambda≥(1/δ)^(-1/3)`, `alpha≤1/4`, and the stated logarithmic broadness budget, it proves the literal normalized low/high alternative. The same original tube indices are used throughout. The support is the finite set of cells with positive actual full-shading intersection measure. Full and marked probabilities are the actual normalized cell weights, multiplied by each row's common-mean factor.

The low branch proves

`#low ≥ [(1/ratio)*(xi*lambda*M/delta)] / [2*64*(n+5)*log(2/delta)]`.

Here `ratio=C₀/min(c₀,1)` and low cells are defined by strictly positive normalized expected marked mass below `64*(n+5)*log(2/delta)`.

The high branch `HighResult` constructs an actual dyadic depth `J`, with `δ≤radius J 0<2δ` and `J≤log(1/δ)/log 2`, and one outcome satisfying both `SampleGood` and the per-tube band `[2*mu/3,4*mu/3]`. Its spatial masks are exactly the support-centered dyadic balls. Its angular masks are the original-direction-centered open doubled-theta caps. Its ball cutoff is exactly

`ballCoefficient n * B * testRadius^alpha * fullMean p i`,

where `ballCoefficient n=4*(1+(n+1)/2)`.

Both branches also receive actual theta positivity, `δ≤2theta≤1`, and its fixed logarithmic lower bound. The theta choice is `SamplingTheta.choice (ratio*K) beta`.

## What was discharged

No finite support cardinality, test count, expected ball/cap mass, failure budget, good event, or narrow density conclusion is assumed. Direction count comes from actual projective cap packing; support and test counts come from bounded original carriers and actual grid geometry. The normalized means module supplies exact mass and integrated physical two-ends/broadness estimates. The finite sharp sampling theorem supplies the actual outcome after these premises have all been proved.

The geometric grid coefficient is `5^(n+1)*(1+regionRadius(width+(n+1)/2,baseR))^(n+1)`. The uniform scale threshold combines only its finite sampling threshold and the fixed logarithmic theta threshold. It does not depend on the configuration, `M`, `lambda`, `xi`, `B`, `alpha`, or actual `K` within the fixed budget.

## Remaining integration boundary

This module proves the Section 6 sampling assembly, not the resulting pivot inequality. Root-owned `SamplingRealization`, `SamplingPivotInterface`, and `SampledMarkedEstimate` perform the actual sampled family conversion and pivot application. The small-density branch `lambda<(1/delta)^(-1/3)` and conversion of the low-cell count into the desired original-union estimate remain outside this module. Measurable density, original separation, physical two ends, and broadness are explicit input hypotheses, not conclusions.

## Validation

- Clean original source compile and `.olean` build.
- Exact full-source audit: 3 theorems, 6 definitions, 9 named declarations.
- No warnings or errors.
- Mathematical review checked actual ambient exponent `(n+1)-1=n`, logarithm `log(2*N)=log(2/delta)`, fixed cutoff coefficient, same outcome for the wide and narrow bands, and the direction of the low-mass lower-bound transfer.

Source SHA-256: `33785372f6f91406ea727a43576c756355e1ca454380f8c2a9933da435f53ad6`.
