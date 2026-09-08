# Separate geometry review of exact bush length normalization

Read `BushLengths.lean` at SHA `9d7b3b280e93affa08115c1e9c097422157997c722a5a670cb64692020d667a9` without editing the source. No mathematical or statement-scope defect was found in `cumulative`.

This is the direct no-error adapter that the earlier generic positive-error cumulative wrapper did not itself expose. It fixes ambient dimension, width, upper axis length and `m>0` before the positive coefficient, then all actual original rows, individual lengths, scale, cumulative density and cap coefficient. There is no two-ends, direction-separation, bounded-position or per-row density hypothesis.

The proof uses the single fixed `W=max 1 lengthUpper`, retains every original integer shade and the exact old union, and applies the actual bush theorem at `delta/W` and `s/W`. The cumulative ratio `(s/W)/(delta/W)` is exactly `s/delta`; no incidence mass is lost. Original variable-length carrier membership gives normalized unit-carrier membership by actual geometry. The cap bound at the lower mesh is transported with the explicit positive real exponent `m`.

The resulting fixed coefficient contains both powers of `1/W`, with exponents `m/2-1` and `(m+2)/2`; their product has no variable-scale dependence. The second exponent is positive, so the separate `s=0` branch reduces to zero rather than relying on an invalid division by density. The `M=0` branch is also explicit. Negative or zero individual axis lengths need no extra convention: actual carrier membership forces any impossible row to be empty. A positive lower length is not needed for this discrete cardinality statement.

The conclusion has no epsilon or logarithmic error and the original `s<=1` range. It therefore closes the optional bounded-variable-length form of Appendix A.1 while preserving its original no-error strength. This new module is outside the already published 381-module checkpoint 21; it should be registered in a later checkpoint rather than retroactively attributed to that snapshot.
