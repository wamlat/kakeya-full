# Gaussian projection route: first probabilistic core

Source: combined PDF §2.1, text lines 219–278, especially collision bound (2.3). The conclusion (2.2) was already proved by the separate `ProjectionConclusion` route. This work verifies additional content of the manuscript's Gaussian proof; it is not required to recover that already-proved conclusion.

## Actual results now proved

- `GaussianMatrix` samples the Euclidean space of the **35 original entries** with its standard Gaussian probability measure. The original entry map has the product of 35 real N(0,1) laws. The matrix-vector formula is the actual sum over seven columns. The joint Gaussian law is proved before zero cross-covariance is used for independence. For any fixed orthogonal unit vectors in R7, their images have exactly the product of two standard Gaussian R5 laws.
- `GaussianSmallBall` proves the actual real Gaussian density is at most one, bounds a Gaussian n-dimensional closed ball by its enclosing coordinate box, and obtains `min(1, ofReal((2*r)^n))`. It assumes no small-ball bound as input.
- `GaussianPerpendicular` derives the target law of an actual linear coisometry from its adjoint norm identity, applies this to tail coordinates and the actual `alignStem` isometry, and identifies the resulting norm with the true orthogonal remainder `y - inner(u,y)*u` for unit u. In R5 its probability is at most `min(1, ofReal(16*r^4))`, uniformly in every fixed u.
- `GaussianConditioning` uses the explicit Borel map `x -> x/||x||` outside zero (with a fixed unit value at zero), proves joint measurability of the intrinsic perpendicular remainder, and applies Fubini. For every measurable first-image event B, the actual matrix probability of `Pv in B` and a perpendicular remainder at most r is at most `Gaussian5(B) * min(1, ofReal(16*r^4))`. Neither a conditional-law hypothesis nor a measurable choice of frames is assumed. The zero extension is defined explicitly; nonzero images have the usual geometric interpretation.

## Verification and frozen files

All four modules compile to .olean with zero diagnostics. Each named local definition/theorem/instance was checked against the **entire exact source**, and all dependencies use only standard foundations (`propext`, `Classical.choice`, `Quot.sound`). These named checks total 42 declarations; root is separately running the broader production inventory including generated local declarations.

| Module | Named audited declarations | SHA-256 |
|---|---:|---|
| `GaussianMatrix.lean` | 17 | `e6e69c216aad017867923d0991122013f6422bea95755fae5229cd7475892d41` |
| `GaussianSmallBall.lean` | 4 | `52d629b302106f365bdaba0095920874171db0e622fdf6377099b9c67909c0b0` |
| `GaussianPerpendicular.lean` | 11 | `986aacd78d413c68144cdffd36b1974bce03d4b626385cf17db207e635abd2c3` |
| `GaussianConditioning.lean` | 10 | `3acae884727b924ca32bbcd65d3c0dd4d678253f282f6c7a1ff7c757f19f2cdc` |

Individual exact-source audit evidence is in `<Module>_full_source_audit.{lean,json,log}` in `audit_work/`. None of the frozen checkpoint20 sources or shared registries was edited.

## Remaining route boundary at this freeze

The four modules alone do **not** assert the truncated angular-collision estimate (2.3): the deterministic implication from bounded operator norm and small projected angle is being constructed separately in `GaussianCollisionGeometry`/`GaussianCollision`, using root's actual `ProjectiveAngleComparison`. Root separately constructs the bounded-matrix/many-long-images positive-probability event. Simultaneous realization, collision graph selection and exact projected shading preservation are later parts of the Gaussian route, not outputs of these four modules.
