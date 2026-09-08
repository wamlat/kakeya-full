# Independent finite-agent review: actual Gaussian projection closing chain

Read every statement and proof of the three frozen modules below, against the actual GaussianProjectedFamily.Output fields, the original-length lower-density adapter, the geometric separation-to-cap theorem, and source §2.1 equations(2.2)–(2.4). **No substantive defect found.** Sources were not edited and no production audit was duplicated.

| Source | SHA-256 |
|---|---|
| `GaussianProjectionSeed.lean` | `5344667dc4cb6ff8f50b551288d4f18b0648116f6533a6b5284df7244d9f1357` |
| `GaussianProjectionAlgebra.lean` | `f7a878509cadd52338bf88d3e0620a99b95fbfd00d37d7f02cff1991edf7fa23` |
| `FiveDimensionalLengthSeed.lean` | `f33ecf1b83994d21a25f32d0c31cd822f0471784d523b01b0c6a3976b9d3a1e3` |

## Actual target family and the five-dimensional estimate

GaussianProjectionSeed.original_rows constructs the actual Gaussian-selected Output from the original family. Its target normalization is exactly width20w+5/2, projective separation2/pi, and base radius20R; positivity follows from fixed w,R>0. The actual physical length function has upper bound20. These are precisely the fields proved by GaussianProjectedFamily, at the same original mesh delta. No target shadings, geometry or population are supplied as assumptions.

The fixed positive fiber constant is `fiberConstant 7 5 (1/4) 20 width`. Original row lower density lambda/delta and the actual image-row bound imply `(1/Cfiber)*lambda/delta` for each selected target row. The seed fixes crow=1/Cfiber before all configurations. It needs no strict factor-two output normalization, row upper bound, or lambda<=1; the original image rows are used intact.

FiveDimensionalLengthSeed derives DiscreteEstimate(5,4,7/2,7/2) from the already proved fractional seed. Its separation hypothesis constructs the full target cap coefficient with exponent4 and absorbs that fixed coefficient into c. Consequently no original A enters this target seed: the original inverse-A loss occurs exactly once, through the actual retained population. Its bounded-length adapter preserves the original target integer labels and union. There is no external seed axiom or desired projected-estimate premise.

## Quantitative closing and uniformity

The selected population is at least `retainedConstant*M/[A log(2/delta)]`. The target seed is used at eta=eps/2 and gives delta^(1/2+eta)*lambda^(7/2) times that population. GaussianProjectionAlgebra.inverse_log_delta chooses ell>0 before every delta in(0,1], with `ell*delta^eta <= 1/log(2/delta)`. This follows from the proved uniform log-loss theorem at N=1/delta, including scales near1.

The closing theorem multiplies only nonnegative factors and uses the exact identity `(1/2+eta)+eta=1/2+2eta`. Substitution eta=eps/2 produces the claimed final delta^(1/2+eps), retains lambda^(7/2), and leaves a single A inverse. Its optional scalar hypotheses do not secretly require eta>0 or ell>0: the inequality is valid as stated, and the actual caller supplies both positivity facts through the prior choices. No division by M or the selected population is performed; M=0 is included. The actual target union cardinality is bounded by the original F.unionCells cardinality before closing.

The final c is the product of the fixed target seed constant, globally fixed retainedConstant, and uniform ell. Every factor is chosen before M,F,delta,lambda,A. No variable cap, density, family or logarithmic quantity is absorbed into it.

## Exact proved scope

`original_rows` is the completed actual Gaussian-route **positive lower density on every original row** estimate, with output `c A^-1 delta^(1/2+eps) lambda^(7/2) M <= #F.unionCells`. It accepts arbitrary positive lambda and only a lower row bound; the family is bounded/admissible and direction-separated with the original cap-four condition.

Literal equation(2.2) allows arbitrary/empty rows and total cumulative incidence, and weakens the density exponent to7/2+e. That conclusion requires the separate cumulative/Corollary1.1 assembly; it is not falsely asserted by these three files. The same conclusion was already proved earlier by ProjectionConclusion through a different seed route, and the current cumulative wrapper is now being added to the actual Gaussian route. This is a precise scope boundary, not a defect in the present theorem or an additional gap in the already-proved conclusion.
