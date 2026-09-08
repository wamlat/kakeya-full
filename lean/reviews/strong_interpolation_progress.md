# Constructive second interpolation stage

The five new modules listed below are frozen, clean-built and fully audited. They prove the actual strong L1/Lr interpolation step used in manuscript Section9.3, without a custom interpolation axiom or a desired moment-bound premise on intermediate truncations.

`StrongInterpolation.strong_interpolation` accepts an operator T with the shared proved PositiveLaws interface, measurable outputs for measurable inputs, real parameters1<a<r and c>0, and explicit strong endpoint integral bounds

`∫Tg ≤ ofReal(A1)∫g`,
`∫(Tg)^r ≤ ofReal(B)∫g^r`

for every measurable ENNReal-valued g. A1 and B need only be nonnegative. The input measure is SFinite, as used by Tonelli; the output measure is arbitrary. The conclusion for every measurable ENNReal f is

`∫(Tf)^a ≤ ofReal[2a A1 c^(1−a)/(a−1) + 2^r a B c^(r−a)/(r−a)] ∫f^a`.

Here B is the strong-r INTEGRAL coefficient, namely the rth power of an operator norm coefficient. The entire statement allows infinite input values and input/output integrals. No input norm is divided out, and no unproved infinite quantity is converted toReal. PositiveLaws is the existing elementary-law record; this proof uses its finite measurable-input subadditivity field. Its additional elementary laws are already proved for the actual Kakeya operator. The endpoint bounds remain visible hypotheses, to be discharged by KakeyaOperatorL1 and RestrictedStrong in the final operator assembly.

The proof constructs the literal high part f*1_{f>ct} and low part f*1_{f≤ct}. They form an exact pointwise partition, including equality at the threshold and infinity. The strict output t-level is covered by the two actual output t/2-levels. Markov is applied to the constructed measurable outputs, with positive finite scalar thresholds. Thus it yields the correct factors2 and2^r.

The shared ENNReal power-layer-cake extension proves the full integral/strict-tail identity by monotone min(f,n) truncations; it needs no finite-output assumption. The pointwise high power kernel integrates over(0,u/c), producing c^(1−a)/(a−1) timesu^a. The low kernel integrates over[u/c,infinity); its endpoint singleton is Lebesgue-null and the upper power tail converges because a<r, producing c^(r−a)/(r−a) timesu^a. Zero and infinity are handled separately before a finite positive toReal representation is used. In particular, at u=infinity the low kernel is zero; the general theorem correctly states an inequality, not a false equality to infinity.

Both actual kernels are jointly measurable in the scalar threshold and spatial input. Tonelli interchanges the nonnegative integrals, and the scalar kernel bounds yield the two terms of the announced coefficient. This derives the truncation estimates rather than assuming either truncation belongs to an endpoint Lp space. Constants are fixed before f; all scalar algebra retains the exact displayed coefficient.

The separate root-owned StrongInterpolationAlgebra will balance c=(A1/B)^(1/(r−1)) and perform the final scale conversion. Those optimizations and the final eLpNorm/actual-operator assembly are not asserted by these five modules.

Independent mathematical reviews were also completed: scalar agent reviewed the layer-cake, truncation, power-kernel, Tonelli and final interpolation statements and found no substantive defect. Reports: ennreal_layer_cake_independent_review.md, strong_truncation_independent_review.md, and strong_interpolation_independent_review.md. Our separate reviews of the upstream finite restricted interpolation and actual dyadic extension are in restricted_interpolation_independent_review.md and dyadic_extension_independent_review.md.

Verification for final exact bytes: every module compiles with zero diagnostics; each full-source environment audit contains only propext, Classical.choice and Quot.sound, no custom axiom or admitted proof. Audit source copies, logs and JSON evidence use each module name with SourceAudit.lean, _axioms.log and _audit.json suffixes.

| Module | Source theorems | Local declarations | SHA-256 |
|---|---:|---:|---|
| ENNRealLayerCake | 7 | 10 | `33f4b0cd579326772d22d39186b7881d16f1c58520c6657974eefa83721bb8e2` |
| StrongTruncation | 6 | 10 | `567c000221045298e64f4e4004be424869a8ec5d432723b6ac222ca676ddd914` |
| TruncationKernels | 4 | 4 | `5783a9000fedf612202b81ed5bb85cd9984843cffc8bb99348082980cf1ec87a` |
| TruncationIntegral | 6 | 6 | `0e1f2fde92fcb593b7df637b742e76c08383afc7f5a824b2a8aa4f26cec86299` |
| StrongInterpolation | 4 | 6 | `81818f8e0b2e18e00924f79e02bad5392d7ea824376c07f3155a43dc29c2e38a` |

Total: 27 named source theorems, 4 definitions, 36 audited local declarations, including 32 theorem declarations. All work is outside frozen checkpoint18; no existing frozen module or registry was edited.
