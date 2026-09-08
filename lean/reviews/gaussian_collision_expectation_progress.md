# Actual expected Gaussian collision count

Source: combined PDF §2.1 after equation(2.3), in the Gaussian proof of Lemma2.1. This report extends the completed collision probability, not the already separately proved conclusion(2.2).

## Literal final theorem

`GaussianCollisionExpectation.expected_count_bound` proves

`integral collisionCount(F,K,delta) <= ofReal(C(K) * A * M * log(2/delta))`

for every actual `TubeFamily 7 M`, K>=0, 0<delta<=1, A>=0, original delta-projective-chord separation, and original cap-four bound. `collisionCount` is the ENNReal cast of the cardinality of `orderedCollisions`: a **literal finite set of original ordered pairs (i,j), i!=j**, both images nonzero, original matrix operator norm<=K, and actual projected angular separation<=delta. No count, per-pair probability, summed kernel, or expected-value estimate is supplied as a premise.

The explicit coefficient, fixed before every family/scale/population/cap input, is

`C(K) = max(1,16*(pi*K/2)^4) * (48*packingConstant(6)/log(2)) > 0`.

Empty families and zero cap coefficients are included; no division by M or A occurs. This is the ordered count, so both (i,j) and (j,i) occur when a distinct pair collides. The diagonal is excluded in the actual random set. It is included only in the nonnegative comparison kernel, where its contribution is harmless.

## Constructed direction-kernel geometry

`GaussianCollisionKernel.family_row_bound` proves

`sum_j (delta/max(chord(v_j,v_i),delta))^4 <= (48*packingConstant(k)/log(2))*A*log(2/delta)`.

It reuses the previously proved **finite dyadic shell cover and explicit terminal depth**, then proves each actual shell costs at most16 times the cap coefficient. For radii<=1 it uses the original cap-four hypothesis. For radii>1 it derives total population from `CapCover.cap_bound_total_count`, whose finite radius-one covering net is constructed geometrically; no additional population oracle is assumed. The depth bound is explicitly transported to the natural logarithm, including scales near1 where log(2/delta) is positive.

The expectation module uses original separation and the proved chord<=angle comparison to control every distinct pair by that actual chord kernel. Exact finite indicator summation proves the integral equals the sum of the actual pair probabilities. All events and the random finite count are measurable.

## Verification

Both files are frozen and compile with zero diagnostics to their .oleans. Exact full-source named-declaration checks pass, standard foundations only (`propext`, `Classical.choice`, `Quot.sound`). These are 21 named declarations; root handles the additional generated-declaration production inventory independently.

| Module | Named audited declarations | SHA-256 |
|---|---:|---|
| `GaussianCollisionKernel.lean` | 9 | `53fe88861368bbcf8b4654fac0d50b0ada5f4f6ac4201ec6b85b263b86f8c69a` |
| `GaussianCollisionExpectation.lean` | 12 | `dcac07519daaee00d02444be030a492ab4ecec97adc5659cb11b34536c8a25dd` |

Evidence: `<Module>_full_source_audit.{lean,json,log}` in `audit_work/`. No frozen/shared source or registry was changed.

## Remaining original-route interfaces

This supplies the quantitative random collision input for a simultaneous realization with root's bounded-matrix/many-long-images event, and thereafter a collision-graph independent set. The actual projection of finite shadings, its controlled grid fibers, and final projected-family normalization remain separate deterministic geometric tasks. None is assumed in these expectation statements. The scalar conclusion(2.2) remains already independently proved by ProjectionConclusion.
