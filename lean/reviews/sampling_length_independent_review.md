# Independent review: literal sampling geometric extension

Read all six frozen sources below against manuscript Lemma6.1, equations(6.1)–(6.19), and the existing raw sampling, exact probability, cell geometry and realization interfaces. **No mathematical defect or remaining sampling-normalization gap was found within the stated Euclidean half-open-grid/projective-chord conventions.** This supplements `sampling_raw_independent_review.md`, which independently checked the first four raw full-range modules.

## Original geometry and probabilities

`lengthCarrier` is the literal finite segment parameter interval [0,length_i], with the original base and unit direction. The final Input requires only a fixed upper length and fixed upper width, so the source's comparable-length/width inputs are included. Its full support radius follows from these actual carriers, bounded original bases and δ≤1. No common support/cardinality or geometric outcome premise is supplied.

`SamplingBoundedSupport.support` is the actual finite set of positive original full-intersection cells, with membership proved equivalent to such a positive intersection. Every positive cell lies in the explicitly constructed bounded grid box. Candidate cells cover all original points, including grid boundaries, and omitting zero intersections loses neither full nor marked mass. The full and marked means are exactly their original measurable volumes divided by δ^(n+1).

The final rawFull/rawMarked arrays use these original intersections and original δ, without row equalization or spatial normalization. The separate common-homothety lemmas in SamplingGeometry are valid exact identities but are not used to replace the final arrays, angles or mesh. Nested probabilities follow from literal G_i⊆Full_i and cell volume. Actual independent coupled sampling is inherited from the previously reviewed probability core, not assumed in the final output.

## Test families and uniform threshold

Actual sep*δ-separated directions give M≤packingConstant(n)*sep^(-n)*δ^(-n) in ambient n+1; the fixed threshold also enforces δ≤1/sep. The actual bounded support supplies O(δ^(-(n+1))) cells and support-centered dyadic tests of size O(δ^(-(n+1))*log(1/δ)). Every nonempty arbitrary-ball intersection selects an actual support center; all its labels lie in the associated test with radius≤4r. Empty intersections need no test. Physical means use enlarged balls only, with total shading mass above radius one; there is no sub-mesh two-ends premise.

The full mean lower bound is c₀λ/δ, and the ball cutoff is a fixed-dimensional factor times B*r^alpha times that same raw full mean. The two relevant powers are N^(1-s) and N^(1-s-alpha), both positive in the displayed 0<s<1 and 0≤alpha<1-s range. Counts and every failure budget are discharged by the previously proved exact sampling theorem. The chosen δ₀ precedes every original family, per-tube length, Full/G, λ, ξ, B and K. Upper logarithmic B and lower logarithmic ξ assumptions are unnecessary for this existence proof; omitting them strengthens the source range. The K upper logarithmic budget is used to ensure δ≤2theta uniformly.

## Exact closed caps and one unchanged outcome

The cap tests are centered at all original tube directions, so their number is exactly M. For a closed chord cap of radius0<theta≤1 on the unit sphere, the proof gives ||a-b||²≤4theta²-theta⁴<4theta². Choosing signs transfers this strict diameter bound to projective directions. Consequently each nonempty closed theta-cap is contained in an EXISTING open2theta test centered at one of its actual members. Closed-cap broadness at exactly the source theta therefore follows without changing theta, probabilities or the outcome. Unit cap centers are explicitly required in the closed statement.

The Output stores one omega on the original tube/support pairs, its SampleGood certificate and its sharper2/3..4/3 raw-mean band. Its family and marks are literal images of fullShading/markedShading under the injective original-label embedding. This preserves counts exactly, leaves every original axis and index unchanged, and derives every final guarantee from that same omega:

- c₀λ/(2δ)≤#Y_i≤2C₀λ/δ;
- sum_i#H_i≥Wg/4≥[ξ/(8C₀)]sum_i#Y_i, with the exact original Wg and the middle inequality separately proved;
- full two ends at all δ≤r≤1, with coefficient32(1+(n+1)/2)B for alpha≤1;
- each selected center remains within the fixed cell-width enlargement of a point with parameter in its ORIGINAL [0,length_i] interval;
- actual fixed longitudinal-mesh interval counts, own positive full/marked intersections, marks⊆full, unchanged separation and optional cap coefficient;
- actual union count≤available support count and selected whole-cell union⊆available whole-cell union. No false inclusion into the original measurable union is asserted.

The deterministic low branch likewise uses the exact Wg, the actual positive low cells, Wg/2 retained expected marks and Wg/(2 threshold) cell count. The final theorem constructs low or a nonempty certified Output; a desired outcome is not a caller hypothesis.

## Scope and validation

These modules close the earlier fixed-length/separation/open-cap caveats in the raw sampling report. They use explicit unit-direction/projective-chord conventions, actual finite segment lengths and centered half-open grid cells. They do not claim an equality with every other angle-metric convention without a comparison. Such convention bookkeeping is distinct from a missing sampling theorem.

Independently checked all final hashes against the existing audit metadata and verified each audit source begins with the complete final source. All163 audited declarations (131 theorem entries,54 named theorems) have only propext, Classical.choice and Quot.sound; metadata reports no custom axiom or diagnostic. The final SamplingLengthRealization source was also independently recompiled cleanly. No frozen source was edited.

| Module | Final SHA256 |
|---|---|
| SamplingClosedCaps | `e0601e7655fb29cd4069c6c2c1649cb05564d6f61879db20f241ec1d410e3d03` |
| SamplingGeometry | `726dde39fb3915ff83e1b9991e2e4d5ffd33747d72d019285190e4609ef06e0a` |
| SamplingBoundedSupport | `b1313fee65ab09892edfcfec27b6dd3961199ef348e4427901afe93e4ad0e56c` |
| SamplingLengthInput | `2aa8f1437ee876da5a3ab444af27e89a77703bc78234b66d039fb0dc7c92c0e4` |
| SamplingLengthAssembly | `7c1955db5eafd5d0939865afd50c938c1e971a07eb71babf7970d56fb82ef3cc` |
| SamplingLengthRealization | `1732e22b425ac9321b2fc8edbbdd9eec6a06d27df0afb9997fecbc28409cfaa6` |
