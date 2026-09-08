# Literal first-step logarithmic estimate with all fixed conventions

Both new sources compile clean and passed unchanged-source production audits:

| Module | SHA-256 | Audit |
|---|---|---|
| LogarithmicLengthEstimates | 6a4c9c352ea8d5769beea554d3b3a0fccaeec492297ed7bf08d2bc1c721b9068 | 5 named, 13 local theorem, 14 all declarations; standard-only |
| SixDimensionalLogarithmicLengths | a4b219785138dc9b83af8d790eb4ce0a8cd271277e52f6470652da5119f891dc | 2 named, 2 local theorem, 2 all declarations; standard-only |

Evidence: `logarithmic_length_estimates_audit.json`, the two corresponding `_SourceAudit.log` files, and final-byte independent review `logarithmic_lengths_geometry_review.md`. Lean4.33.1 and the pinned mathlib revision are unchanged. Earlier frozen sources, including LogarithmicTwoEnds and SixDimensionalLogarithmic, were not edited.

`LogarithmicLengthEstimates.estimate` consumes the proved fixed-coefficient `TwoEndsDiscreteEstimate (k+1) m D C`, with m>=0 and C>=1. For every fixed original normalization, upper axis length, positive lower/upper row multiples c0,C0, B0>=1, alpha>0, log exponent b>=0 and scale error eps>0, it chooses c>0 before any actual original family, individual lengths, scale, density and cap coefficient. Its data are actual old-cell incidence in original variable-length carriers, original separation/bounded bases/cap, row counts between c0*lambda/delta and C0*lambda/delta, and original two ends with coefficient B0*log(2/delta)^b. It concludes the original union count bound at the SAME set exponent D and density exponent C.

The fixed homothety W=max(1,lengthUpper) changes mesh and density to delta/W and lambda/W. The common original integer labels and union are unchanged. The smaller-scale cap bound, separation, carrier geometry and base bound are actual proved adapters. The fixed alpha is weakened to min(alpha,1) before constants. The scalar factor is exactly W^(-(m-D+eps))*W^(-C).

A genuine boundary issue is handled explicitly: log(2/delta) can be below one at coarse mesh, so B0>=1 alone does not imply B0*log(2/delta)^b>=1. `logFactor b=max(1,(log 2)^(-b))` enlarges B0 by one FIXED factor. The proof uses log(2/delta)>=log2>0 to establish the required per-configuration coefficient>=1 for the actual length two-ends adapter. It then proves log(2/delta)<=log(2/(delta/W)) and applies the logarithmic wide-density theorem at fixed new prefactor B0*logFactor(b)*W. No analytic estimate receives a configuration-dependent supposedly fixed B.

`SixDimensionalLogarithmicLengths.cap_free` supplies the actual six-dimensional two-ends theorem and derives cap5 internally from original fixed direction separation. No cap premise remains. `source_notation` states precisely

`E >= c * N^(33/8-eps) * lambda^(15/4) * (M/N^5)`

for N>=1, positive lambda<=1, original B0*log(2N)^b full two ends, arbitrary fixed c0,C0, width/separation/bounded-region parameters and individual lengths at most the fixed upper bound. It retains the literal original union, with no angular, marked, sampling, energy, normalized-family or retained-count premise. Positive fixed lower lengths from the manuscript are included by this stronger upper-length-only carrier statement. Thus first-step Lemma6/(25), including the logarithmic coefficient and fixed convention changes, is now an actual direct consumer.

Compilation commands (development project):

```
lake env lean -o .lake/build/lib/lean/LogarithmicLengthEstimates.olean LogarithmicLengthEstimates.lean
lake env lean -o .lake/build/lib/lean/SixDimensionalLogarithmicLengths.olean SixDimensionalLogarithmicLengths.lean
python3 ../audit_logarithmic_length_estimates.py
```

Integrated verification/publication of the enlarged snapshot remains the parent's separate gate.
