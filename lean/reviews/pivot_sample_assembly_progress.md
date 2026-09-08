# Actual marked angles, legal samples, and output selection

The root-owned development connects eight modules:
`LegalSampleNormalization`, `TransverseAngles`, `LegalAngleSamples`,
`LegalAngleNormalization`, `LegalLabeledSamples`, `LegalSampleOutputs`,
`LegalSampleSelection`, and `MarkedLegalSamples`. The delivered manifest is the
authority for their frozen source hashes and full Lean logical-dependency audit.

## Actual geometry and labels

`TransverseAngles.angles` is an actual finite set of marked occupied cells and
ordered incident tube indices. A true half-cap condition retains at least half
the ordered pairs at each cell. Cauchy–Schwarz gives at least `I^2/(2E)` angles
from marked incidence mass at least I and at most E marked cells. Projective
chord separation `2 kappa` implies perpendicular-axis norm at least kappa.
Each angle has distinct original tube indices and a common actual shaded-cell
center, whose tube membership follows from original admissibility.

`LegalAngleSamples.construct` constructs one sample system across every such
angle. Each angle uses one sign for its first axis and at least
`(lambda/delta)^3/128` actual original ordered label triples. Original physical
two ends, not a supplied interval or sample count, gives their coordinate
separation. The intermediate projection is fixed by its original label.

One common homothety `R=1+2 width` sends every raw angle to the normalized
`PivotWitnesses.Angle` and `Endpoints` types at mesh `delta/R` and parameter
`kappa/R`. Actual endpoint, intermediate and pivot points are proved to undergo
that same homothety. All original integer cell labels are unchanged.

`LegalLabeledSamples` supplies actual grid-to-projection error at most
`2 width delta/R`, and constructs the finite dependent labeled-pair sets used
by `PivotOutputCount`. The record map from original triples is injective, with
an exact left inverse recovering the original intermediate/first/second labels.
All records belong to the constructed finite sets. Proof wrappers and repeated
projection coordinates add no multiplicity.

## Complete original-sample output bounds

`LegalSampleOutputs.output` is a deterministic pair of actual normalized pivot
cell label and original intermediate label, with the same `Cell k × Cell k`
output type for every marked angle. Outside its finite valid sample set it has
an irrelevant default value; every counting theorem restricts to valid samples.

Let `box(k,w)=(2 ceil(w+1)+3)^k` and
`fiberConstant(k,w)=3(2k+4)box(k,w)^2`. The exact original-sample bounds are:

* outputs per angle <= `8 box(k,k/2) R lambda/delta^2`, for comparable original
  shadings;
* samples in each complete output fiber <=
  `fiberConstant(k,2 width) R^2/(kappa delta)`;
* the ceiling of that last bound is a proved integer fiber budget.

These follow through `RawSampleTransfer` from actual geometric interval and
grid counting. They are not additional count hypotheses. A complete output
fixes precisely one intermediate label and one angle-specific endpoint fiber.

`LegalSampleSelection.dyadic_selection` substitutes these geometric budgets
into actual low-fiber deletion and a single global integer dyadic selection.
Writing `D=8 box(k,k/2)R`, the chosen low-fiber cutoff is
`t=lambda^2/(256 D delta)`. Its product with the output budget is exactly half
the cubic sample budget. The theorem returns the actual whole-edge set Omega,
one integer `h=2^j`, the exact size-bin membership, nonemptiness, `t/2<h`, the
integer upper bound, and the explicit retained sample and edge-count estimates.
It requires a nonempty actual angle set, not an assumed fiber population.

`MarkedLegalSamples.construct` uses the same explicit `PivotKappa.choice` for
the original two-ends exclusion and pointwise cap half-test. It derives both
the legal sample system and the nonempty transverse angle count from original
marked incidence, physical two ends, and cap broadness. Its remaining scale
condition is `delta<=kappa`; `PivotKappaScale` supplies a uniform small-scale
threshold from polynomial logarithmic coefficient budgets.

## Scope remaining

This closes the construction and geometric budgets for the legal sample and
global integer-bin stages. It does not prove the complete original marked
sampling/pruning assembly, the collision row count, the final lifted-cell
population and support construction, or the assembled pivot theorem. The
per-output second-tube direction choice and exact collision energy estimates
remain distinct geometric steps. All facts about actual labels, projections,
finite records and constants above refer to these precise module statements.
