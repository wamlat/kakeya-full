# Independent review: SamplingThreshold and SamplingCapTests

Read-only mathematical statement/proof review against combined PDF Section 6 and SamplingApplication. No substantive defect or circular dependency found. Fresh combined full-source audit is recorded separately, checking all 16 local declarations (9 threshold, 7 cap).

## Uniform threshold

source_sampling chooses N0 solely from fixed dimension/count/mean coefficients, before the scale, finite types, probabilities, masks, high set, density, two-ends coefficient and exponent. The alpha range [0,1/4] is handled uniformly. Positivity of cf and cb is explicit; no hidden lower-mean positivity is inferred from a zero coefficient.

Actual source tube-ball count is bounded by a fixed constant times N^(2n): tube count N^(n-1), ball count N^n(log N/log 2+1), and the logarithm is explicitly weakened to O(N). High-cell/cap count is also bounded by a fixed constant times N^(2n), using #caps <= #tubes. The chosen a0 = 64(n+4) gives a0/8 = 8(n+4) > 2n for every natural ambient n. This remains sufficient when the root's original-direction tests replace the source net; there is no assumption that the number of cap tests has the smaller original net exponent.

The density threshold lambda >= N^(-1/3) yields mean growth N^(2/3). The lower test radius r >= 1/N and alpha <= 1/4 yield r^alpha >= N^(-1/4), hence the full ball threshold grows at least N^(5/12). The theorem admits equality at the density threshold, a harmless strengthening of the paper's strict branch. No condition at radii below the mesh is used. Every exponential-budget term is derived from SamplingApplication.failureBudget_le_uniform; the final theorem invokes the actual finite sampling construction. It does not assume an already-good outcome or a failure-budget bound as a premise.

The generic source_sampling interface still explicitly requires the geometric count and expectation inequalities, plus the high-half mass inequality. These are precise assembly inputs supplied by SamplingSupport, SamplingBallTests, SamplingMeans, SamplingTheta and SamplingDichotomy. Treating source_sampling alone as the complete geometric Lemma 6.1 would overstate its scope.

## Actual angular tests

SamplingCapTests uses every original tube direction as one test center. On any nonempty original-radius theta cap intersecting the actual row, it chooses one original direction inside that row; the projective triangle inequality contains the row intersection in the test of radius 2 theta. This gives the exact all-center conclusion, with M actual tests and no net oracle. Strict cap membership is used consistently in the geometric tests and containment. The output statement allows arbitrary center vectors; this is stronger than restricting centers to unit vectors and follows from the same triangle inequality.

The actual sampled marked row is defined from markedShading high omega. At high cells, literal row cardinality and cap cardinality are proved equal to the random-variable counts. At every non-high cell, the marked row is empty; the broadness conclusion is verified directly rather than invoking an unavailable high-cell bound. The resulting cap fraction is exactly 1/10 of actual marked multiplicity, not expected multiplicity or the full row.

## Source hashes

- SamplingThreshold: c64bdcd365558f0614745d17ce0ad1842a673912bd963a14bf5352e81053e717
- SamplingCapTests: a015db6172d1e1da545e582b08c3b5aa20c1db1ae00ab7df18047ba504c50157
