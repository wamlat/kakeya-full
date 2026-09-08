# Independent review: bounded-length cumulative bush estimate

Reviewed `formalization/BushLengths.lean` at SHA-256
`9d7b3b280e93affa08115c1e9c097422157997c722a5a670cb64692020d667a9`.
Read-only review of its full proof, `Bush.cumulative_bush_estimate`, and the
invoked length-normalization algebra found no defect. The parent owns the
production source/dependency audit.

`cumulative` preserves the exact Appendix A.1 exponents
delta^(m/2-1) and s^((m+2)/2), including the error-free form. Its positive
constant is selected using only the fixed dimension, width, upper length,
and m>0, before every family, scale, density, and cap coefficient. The
conclusion concerns the actual original integer union.

The common dilation W=max(1, upperLength) changes delta and s to delta/W
and s/W, leaves all integer labels and their incidence multiplicities
unchanged, and satisfies (s/W)/(delta/W)=s/delta. Actual original
length-carrier membership supplies normalized admissibility. The original
cap coefficient A remains valid at the smaller scale by the proved cap
extension with m>=0. No directional separation, bounded positions,
individual row density, or two-ends premise is introduced.

The transport factor is the positive fixed quantity
(W^-1)^(m/2-1)*(W^-1)^((m+2)/2), equivalently W^-m. The proof uses positive
W and delta, so negative m/2-1 causes no zero-base or sign problem. The s=0
branch is justified by (m+2)/2>0; the M=0 branch is explicit. Only an upper
length bound is needed for this discrete containment argument, without a
positive lower length. Width can be any fixed real number because the
underlying bush theorem itself handles it by widening to max(width,1).
