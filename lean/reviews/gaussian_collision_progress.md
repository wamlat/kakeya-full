# Actual Gaussian truncated collision estimate

Source combined PDF §2.1, equation (2.3), text lines219–278.

`GaussianCollision.collision_probability` now proves for the **actual standard Gaussian5×7matrix** and every pair of original unit vectors v,w with positive unoriented angle psi:

`P[||P|| <= K and Pv != 0 and Pw != 0 and angle(Pv/||Pv||, Pw/||Pw||) <= delta] <= C_K * min(1, (delta/psi)^4)`,

in exact ENNReal probability notation, for all K,delta>=0, with the explicit uniform constant `C_K=max(1,16*(pi*K/2)^4)`. This constant precedes all vectors and collision radii. The nonzero tests are exactly what makes projected directions defined; the source's later retained images of norm>=c>0 automatically satisfy them.

The proof first gives the sharper sine denominator. `GaussianCollisionGeometry.collision_containment` constructs one fixed original unit u orthogonal to v from the actual original v,w and proves for every later actual linear map P that the collision forces `||perpendicular(Pv,Pu)|| <= K*delta/sin(psi)`. Antipodal representatives are handled by actual negation, not a change of original random law. The parent module `ProjectiveAngleComparison` provides the exact decomposition and sine/chord comparisons. `GaussianLinearOperator.operator` is the original matrix as a map on input vectors, definitionally agreeing with `GaussianMatrix.projection`. The previously audited actual joint Gaussian/Fubini small-ball chain then supplies the probability; no collision or expected-count premise is assumed.

The actual event is measurable, including its operator-norm cutoff and both nonzero-output tests. These files compile cleanly and the exact full-source named declaration audits pass under standard foundations only. Root separately handles the broader generated-declaration production audit.

| Module | Named audited declarations | SHA-256 |
|---|---:|---|
| `GaussianCollisionGeometry.lean` | 8 | `b755ed67e50a054197f7048dacfd5b31dfe0d42c204a634add6080d3d67acd97` |
| `GaussianCollision.lean` | 8 | `d10388da3a37a753d11a02639d0429472fb747e02425b3f94571658c4f60a9bb` |

Audit evidence: `<Module>_full_source_audit.{lean,json,log}` in `audit_work/`. Mathematical read-only reviews of the two parent geometric modules are `projective_angle_finite_review.md` and `gaussian_linear_operator_finite_review.md`.

## Remaining original-route steps

Equation(2.3) itself is now proved. The original cap-four/separation hypothesis still has to be summed through dyadic shells to obtain the expected ordered collision count O_K(A M log(2/delta)); this is active new work in GaussianCollisionKernel/Expectation. Root separately handles the positive-probability bounded-matrix/many-long-images event and the graph independent-set bound. Simultaneous realization and exact projected shading preservation are later parts of this alternative Gaussian route. The conclusion(2.2) was already independently established by ProjectionConclusion and is not blocked by these remaining proof-route steps.
