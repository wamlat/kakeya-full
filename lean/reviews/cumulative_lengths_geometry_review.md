# Separate geometry review of cumulative length normalization

Reviewed the frozen production `CumulativeLengths.lean`, SHA `cef706b53546f6c16daaf44b635f4ae6435cdaf180b2ada84df084b23d07ebbc`, read-only. No mathematical or statement-scope defect was found in `from_cumulative`.

The theorem fixes the original geometric normalization, upper length and positive error before every actual family, scale, cumulative density and cap coefficient. It uses one common `W = max 1 lengthUpper`; all original integer rows and their union remain literally unchanged. The normalized scale and cumulative density are respectively `delta/W` and `s/W`, so the original cumulative incidence bound transfers by the same division. Admissibility follows from the actual bounded length-carrier containment. The normalized separation and base radius come from the inherited common homothety, while the real-cap bound at newly smaller radii uses the explicit hypothesis `m >= 0`.

The coefficient includes both actual powers of `1/W`, with exponents `m-d+eps` and `p`; their signs are unrestricted, and positivity follows from `W>0`. The proof does not assume `s>0`, a positive lower length, comparable rows or nonempty population. It inherits the real-power conventions and the complete conditional scope of its input `CumulativeEstimate` rather than introducing an unproved analytic inequality.

This closes the separately named bounded-variable-length **positive-error** cumulative adapter, including the intended Corollary 1.1/4.3 applications once their corresponding proved estimates are supplied. The theorem has `eps>0` in both its input use and conclusion. It should not be described as the exact no-error bounded-length form of Appendix A.1; that requires a direct common-homothety wrapper around `Bush.cumulative_bush_estimate`. Appendix A.1's literal unit-axis statement is already proved. This distinction concerns an optional wider geometry convention, not a missing main conclusion.

The source belongs to development after the frozen 381-module checkpoint 21 and must not be counted retroactively in that freeze. No source, registry, verifier or previous report was edited in this review.
