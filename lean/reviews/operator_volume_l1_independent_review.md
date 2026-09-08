# Independent exact tube-volume and operator L1 review

Read-only final source hashes: TubeIsometryVolume 769b7134ed907e535fd0d14583cbfc7980898bba7a8b8d665333413a8a8dbbf1; KakeyaOperatorL1 6165bffc59ed8c9df0bc53653fa857ec3467f75a70fed73148d29a7b749aa542. No mathematical defect found.

TubeIsometryVolume identifies every actual carrier with the preimage of one reference carrier under translation by the original base followed by the actual orthogonal alignStem map. The map preserves volume and all distances to matching unit-segment parameters, so the volume equality is exact in ENNReal for every real radius. Positive/finiteness assertions add delta>0 only when needed; no unproved real conversion is used.

KakeyaOperatorL1 bounds each carrier integral by the global nonnegative input integral. Because the denominator is the SAME reference volume for every original base/direction, the actual uncountable supremum satisfies the same pointwise bound. Sphere integration costs the finite total sphere measure, giving coefficient sigma(univ)/referenceVolume. Its mesh estimate uses the actual lower volume c*delta^k in ambient k+1, hence the correct loss delta^(-k). Coefficients are finite when delta>0.

For arbitrary nonmeasurable inputs, Mathlib lintegral is the lower nonnegative integral, and monotonicity still proves these inequalities. The header was corrected from 'outer-integral' to 'extended nonnegative integral' during review. Output measurability for measurable inputs is established separately by KakeyaOperatorMeasurability; it is not hidden in the L1 proof. The real normMaximal wrapper applies exactly the same operator to ofReal(abs f).
