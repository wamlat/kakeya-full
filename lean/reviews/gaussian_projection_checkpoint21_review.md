# Checkpoint 21: original Gaussian projection ingredients

**Integrated verification completed:** checkpoint21 passed at 2026-09-07T02:37:57.565354+00:00 with381 modules, 3064 source theorem/lemma declarations, 6170 audited local theorems, 7856 total local declarations and131 exact checks. All41 additions use only standard foundations. The inventory below was prepared while that run was ongoing; its descriptions of that then-pending run are historical. Later Gaussian assembly and net/bush development remains outside this snapshot.

Root read the actual matrix, small-ball, conditioning, collision geometry, probability and expected-count sources, and the final good-direction and projected-family statements. The separate finite, scalar and geometry reviews cover the exact final hashes below. No substantive mathematical defect was found in these reviewed ingredients. This report concerns the frozen 381-module candidate; its integrated audit was still running when the report was prepared.

The sample space is the actual 5-by-7 matrix Euclidean space with its standard Gaussian probability law. Entries, linear projections and the continuous linear operator are concrete. Unit-vector marginals are standard five-dimensional Gaussians. Independence for two orthogonal original vectors is proved via their joint Gaussian covariance; independence of arbitrary original directions is neither asserted nor used.

An actual four-dimensional perpendicular Gaussian small-ball probability is at most min(1,16r^4). The conditioning statement is a product-measure/Fubini estimate for every measurable event in the first projection. No conditioning on a probability-zero point is assumed. A Borel unit direction is defined at zero as well, and the actual collision event explicitly requires both image vectors nonzero.

The projective angle is arccos(abs(inner)), with exact chord=2sin(angle/2), bounds (2/pi)angle<=chord<=angle, and a chosen sign/orthogonal decomposition before any random matrix. Together with the actual operator-norm cutoff this gives source (2.3): probability <= C_K min(1,(delta/psi)^4). The fixed C_K=max(1,16(pi K/2)^4) precedes the directions and scale.

The operator norm is bounded by the actual matrix Euclidean norm. The matrix squared-norm integral is rows*columns, and Markov gives probability(||P||>=20)<=7/80. Actual good original indices have ||Pv||>=1/4; linearity of expectation, without cross-direction independence, gives probability(at least half good and ||P||<=20)>=17/20. The empty family is included.

The exact ordered-collision counter counts distinct ordered original pairs. Its expectation is derived from the actual pair probabilities and the original cap-four hypothesis. The comparison kernel includes the diagonal harmlessly. All dyadic shell endpoints and the radius>1 range are accounted for. The coefficient pays log(2), so the argument never assumes log(2/delta)>=1 when delta is near one. The final expectation is <= C(20) A M log(2/delta).

The finite independent-set result is proved using Mathlib's Turan theorem on the graph complement, with exact size V^2/(V+2e), including V=0. OrderedCount=2e is an identity for the actual graph. This proves the needed graph conclusion by a different route from the source's random ordering.

ProjectedGrid and ProjectedGridFamily use one common rounded image map on all original labels. The actual target union is the image of the original union, hence has no greater cardinality. The original tube parameter geometry bounds each fiber by (2ceil(2width+(d+2Kwidth)/c)+3)^n. Actual projected lengths are ||Pv|| in [c,K], target width is Kwidth+d/2, and the projected base and unit direction are explicit. Density is comparable with a fixed fiber loss; an exact ratio two is not claimed.

Remaining original-route assembly outside this checkpoint: choose ONE bounded map with both enough good directions and a collision bound, extract a separated subset of those actual good indices, feed its projected family into the five-dimensional estimate, and perform the final logarithm/cumulative assembly. Root's GaussianRealization and the subsequent selection modules are active and excluded from this frozen inventory. The Lemma 2.1 conclusion already has a separate proved route in ProjectionConclusion; this remainder is not a missing input of MainMaximal or MainOperator.

| Final source | SHA-256 |
|---|---|
| ProjectiveAngleComparison | cce9de5b8c22b8bfc4801282e01fbe028962266a94dcdca70839121fc3012834 |
| GaussianMatrix | e6e69c216aad017867923d0991122013f6422bea95755fae5229cd7475892d41 |
| GaussianSmallBall | 52d629b302106f365bdaba0095920874171db0e622fdf6377099b9c67909c0b0 |
| GaussianPerpendicular | 986aacd78d413c68144cdffd36b1974bce03d4b626385cf17db207e635abd2c3 |
| GaussianConditioning | 3acae884727b924ca32bbcd65d3c0dd4d678253f282f6c7a1ff7c757f19f2cdc |
| GaussianLinearOperator | 9ca1017e5f66f55d29f68b62e5c1ec2922f50dbd1a6d6ee1c0b8bfec04f582de |
| GaussianMatrixMoments | 6bec03641b26b51e3bc9a3747249664fb5c9d8466063a82176c6ee52dcba5ca5 |
| GaussianCollisionGeometry | b755ed67e50a054197f7048dacfd5b31dfe0d42c204a634add6080d3d67acd97 |
| GaussianCollision | d10388da3a37a753d11a02639d0429472fb747e02425b3f94571658c4f60a9bb |
| GaussianGoodDirections | c76c9a6dabf0f62d3265c609ca542c39df747f2ed3085d098aa5cc162dfd6da9 |
| GaussianCollisionKernel | 53fe88861368bbcf8b4654fac0d50b0ada5f4f6ac4201ec6b85b263b86f8c69a |
| GaussianCollisionExpectation | dcac07519daaee00d02444be030a492ab4ecec97adc5659cb11b34536c8a25dd |
| CollisionIndependentSet | 3d28a164bd567faf3b9a4a9271d452dae6c576b1d67ddadb360f3c08aee7fd5c |
| ProjectedGrid | 7ce2f4373b7ff11280775ead5eed783ef76599fa3d3c69861696babb11807faa |
| ProjectedGridFamily | 92744d3882fc76cb440fb5ffcecab5757adb2857fa371d8a986bfbba3d6d532f |
