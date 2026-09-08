# Actual collision plane and shell direction count

`CollisionPlane.lean` is a root-owned development module, built cleanly and
audited from its full source. It is not part of checkpoint 9. Its later
publication requires a new frozen package build and manifest.

The orthogonal frame is constructed from the original first direction and the
normalized transverse coordinate of the second direction. The proof explicitly
handles a zero transverse coordinate. Both original directions have zero normal
coordinate in this frame. The normal-coordinate map is a contraction.

Three actual point/axis incidences with error at most e and longitudinal
separation at least kappa imply competing direction normal norm at most
3e/kappa. For actual legal samples sharing an output and an original second
tube, original admissibility derives all three errors with e=2 width delta.
The common intermediate label is recovered exactly from the actual output.
Thus the competing first direction lies within 6 width delta/kappa of the
original angle plane.

Crucially, `firstIndices` aggregates the possible original first-tube indices
over **all outputs shared with the fixed original angle**, while keeping the
second original tube fixed. It does not fix one output before counting
directions. This avoids an extra output-count factor in the collision row.

The indexed thick-circle theorem is applied to these actual original indices
after the constructed isometry; original delta separation proves direction
injectivity. For ambient k+2, kappa<=1, delta<=phi, and
6 width delta/kappa<=1/2, `collision_shell_count` proves:

    # {possible first indices with phi <= pd <= 2phi}
      <= 2 circleConstant(k,6 width) phi / (kappa^k delta).

This is the ambient normal-coordinate exponent in combined (5.17): ambient
minus two, with exactly one tangential factor phi/delta. The separate
`collision_cap_count` also handles the bottom cap pd<=delta. No ambient
dimension is replaced by the real cap parameter m.

Remaining: combine this direction count with actual intermediate-label
intersection counts, per-intermediate pivot counts, and common-vertex counts;
then sum the finite dyadic collision shells. The completed row and energy
bound (5.18) is not asserted by this module.
