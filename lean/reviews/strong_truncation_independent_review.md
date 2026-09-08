# Independent review of second-stage truncation and power kernels

Read complete StrongTruncation.lean and TruncationKernels.lean sources. No mathematical or statement defect was found.

StrongTruncation constructs high=f1_{s<f} and low=f1_{f≤s}, which partition every ENNReal value exactly, including f=∞ and arbitrary s. The level cover at t uses actual subadditivity and two thresholds t/2. Power Markov is invoked only with t>0 and exponent>0, so division is by a finite positive coefficient. The endpoint bounds are applied to the constructed measurable truncations, with ENNReal integrals; no unsupported Lp membership or finite integral is assumed.

The finite kernels are scoped honestly to u>0. The high part integrates over (0,u/c), while the low part integrates over [u/c,∞); equality at the cutoff belongs to low and the singleton boundary is removed only through the real volume null-singleton theorem. Exponent conditions a>1 and a<r are exactly those needed for convergence of the two integrals. The low kernel also assumes r>0 so its zero branch has zero rth power. Coefficients c^(1−a)/(a−1) and c^(r−a)/(r−a) match direct integration. Zero and infinite u require the later extension in TruncationIntegral and are not claimed by these finite lemmas.

This review checks statement fidelity and proof structure. Per-file compilation and exact-source audits are maintained separately by the geometry agent. Reviewed source hashes:
- StrongTruncation.lean: `567c000221045298e64f4e4004be424869a8ec5d432723b6ac222ca676ddd914`
- TruncationKernels.lean: `5783a9000fedf612202b81ed5bb85cd9984843cffc8bb99348082980cf1ec87a`


TruncationIntegral.lean was subsequently reviewed at the hash below. No defect was found. Both general kernel statements are inequalities: this is essential for the low kernel at z=∞, where the actual low truncation is zero at each finite threshold while the proposed upper bound is∞. The zero case is treated before toReal and the finite positive case invokes the exact finite kernels. Actual joint kernel measurability is proved and SFinite μ is explicit for Tonelli. Hence no finiteness assumption is smuggled into the integrated high/low bounds.

- TruncationIntegral.lean: `0e1f2fde92fcb593b7df637b742e76c08383afc7f5a824b2a8aa4f26cec86299`
