# Actual sampled original-grid families

SamplingRealization.lean constructs full and marked shadings by mapping the same coupled outcome's finite-support subtype cells to their original integer labels. Tube axes and all tube indices are unchanged by definition. Actual counts are preserved exactly, the full union lies inside the original available support, and marked shadings are contained in full shadings.

The admissibility theorem applies to any sampling probabilities bounded above by the literal normalized original measurable cell weights. Positive selection therefore implies a positive original cell intersection and gives an actual geometric witness within width+n/2 of the unchanged tube. This covers the later per-tube probability normalization as well as unmodified weights.

Exact count and filtered-count identities transfer the SampleGood guarantees to these actual families. Broadness holds at every original integer label and every cap center, including labels outside the support. For cutoff C*B*r_test^alpha*fullMean, the full shadings satisfy all-radius two ends with coefficient (2*4^alpha*C)*B. The finite-to-all-ball enlargement and full mean versus actual shading count are proved inside this transfer.

The usual SampleGood full density interval is still wider than the strict factor-two Comparable predicate. This module does not silently declare comparability. The sharper common-mean sampling normalization is separate ongoing work, needed before applying MarkedPivotEstimate. Likewise a simultaneous good outcome is supplied by the probability construction, not assumed as a final analytic theorem.

Verification: clean build and exact full-source environment audit of all 17 local theorem declarations including generated ones, standard foundations only, no diagnostics or placeholders. SHA-256 07e79d5d80de72c800a1aead4fa53a997bb464a8aff899f281f2b42968416be4. Development after checkpoint 12; the next full manifest governs delivered scope.
