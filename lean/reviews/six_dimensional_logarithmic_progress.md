# Six-dimensional original logarithmic two ends

`SixDimensionalLogarithmic.lean` compiles cleanly at SHA-256 `1e1af2d07c92c93f0aa8b291bea16ecb95e3da0e60fb9e89a9ed1aac0bafd842`. Its complete exact-source audit passes all three local theorem declarations and all three declarations, with standard foundations only.

`configuration_estimate` specializes the actual generic localization theorem to the proved `TwoEndsPivot.six_dimensional`. The output is the original union count lower bound with scale exponent `7/8+eps` and density exponent `15/4`. Geometry, original two-ends exponent, original logarithmic exponent and coefficient, and eps are all fixed before the positive constant and before the actual configuration. No variable coefficient is passed as a fixed parameter to the old two-ends theorem.

`cap_free` obtains the full five-dimensional direction-cap coefficient from the actual separated six-dimensional directions. That coefficient depends only on the fixed direction-separation normalization, so its inverse is absorbed into the fixed positive constant. No cap estimate remains as an input. All original tube axes and integer shading labels are preserved.

`source_notation` proves the actual first-step formula `E >= c N^(33/8-eps) lambda^(15/4) S`, where `S=M/N^5`, with original ball coefficient `B0 log(2N)^b`. It accepts every N>=1, includes the empty family, and has no original marked or broadness hypothesis. The reciprocal-scale and logarithm identities are proved in Lean, not asserted by a notation comment.

This module uses the normalized factor-two `Comparable` rows and unit axes. Actual width, separation and position constants are already arbitrary fixed normalization parameters. A separate log-aware actual trimming and bounded-length adapter is being completed before claiming the broader fixed row/length conventions from the first-step introduction. The main unrestricted result is unaffected by that remaining interface extension. The module lies outside the initial418-source freeze and will enter the final enlarged integrated run.
