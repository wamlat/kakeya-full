# Independent scalar review of simultaneous Gaussian realization

No substantive mathematical defect was found in `GaussianRealization.lean`. I read the final source end-to-end against the actual good-event and collision-expectation APIs previously reviewed. This was read-only; the parent owns its production all-local axiom audit.

Reviewed SHA256: `7ad87b2daf1598494a0c68c2b4bef71da9e913943a84d54958ddb24d6f72ed10`.

The budget is the literal fixed expectationCoefficient(20)*A*M*log(2/delta). For M>0, A>=1 and 0<delta<=1 it is strictly positive, with log(2/delta)>=log 2>0. The coefficient depends only on the fixed norm cutoff and dimensions, before the scale, cap coefficient, family or population.

`excessive` is the measurable event that the actual ENNReal finite ordered-collision cardinality is at least FOUR times that budget. The proof applies ENNReal Markov to the actual count and its proved expected-count bound. The upper comparison is a finite ofReal quantity, making the toReal monotonicity step legitimate. Only after deriving the positive real budget does it cancel to obtain probability <=1/4. There is no expected-count, moment, or failure-probability input.

The simultaneous event is a literal intersection on one original Gaussian sample space: the actual good-direction event, together with actual collisionCount<=four times the budget. The good event is covered by the union of this intersection and the excessive event. Threshold equality may lie in both sets, which is harmless because the proof uses the union upper bound, not a false disjointness identity. The probability calculation is exactly 17/20-1/4=3/5.

The existence theorem chooses ONE matrix from this positive-measure simultaneous event. Its norm bound, good-index count, individual retained image norms and ordered-collision count all use that same outcome and the same original family. The real collision-cardinality output is obtained from the ENNReal bound with a finite threshold; it counts ordered DISTINCT pairs, matching the upstream count convention. The later restriction to good vertices can only lower that count, but this module does not assume or assert graph extraction itself.

The M=0 branch never divides by its zero budget. It obtains an actual bounded matrix through the already proved empty-family good-event theorem, and proves the collision set and real budget both zero by the actual empty index type. Thus the public existence statement includes empty families without weakening any nonempty case or adding a hidden positive-population premise.

The public theorem uses only 0<delta<=1, A>=1, original exact-delta projective-chord separation, and the original cap-four family condition. Unit directions come from the actual UnitTube structure. No cross-direction or cross-pair independence is asserted, and no desired good event, matrix, collision count, or output family is supplied as a premise. It proves the simultaneous existence step at combined.txt lines246–250 following (2.3); collision-graph independent-set extraction and the projected-grid/analytic estimates remain separate downstream constructions.
