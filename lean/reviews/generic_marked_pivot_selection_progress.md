# Actual marked selection with an arbitrary legal pivot radius

`GenericMarkedPivotSelection.lean` adds two input-facing theorems in a new module. No frozen module was changed.

## Arbitrary radius

`GenericMarkedPivotSelection.construct` takes an arbitrary radius 0<kappa≤1 together with three explicit scalar admissibility tests:

- 2kappa≤theta;
- (2width+1)kappa≤1;
- B*((2width+1)kappa)^alpha≤1/16.

The remaining scale condition is the actual collision condition `(6width/kappa)*delta≤1/2`, with width≥1/12 and delta>0. This condition implies delta≤kappa by the existing scalar collision lemma, hence delta≤1. Those two facts are derived inside the proof rather than assumed separately.

The other inputs are the original actual full tube family, comparable full shading density lambda, original delta separation, marks contained in full shadings, marked incidence mass at least I over H, |H|≤E, pointwise half-cap broadness of the marks at theta, and physical two ends for the full shadings. No full-row broadness, legal-sample population, angle-count lower bound, selected-fiber count, output support estimate, or energy estimate is supplied as a hypothesis.

The proof invokes the existing actual `MarkedSubsetSamples.construct`, which constructs a legal sample system S from full shadings while deriving angle population at least I^2/(2E) from marks. It then invokes the actual geometric `PivotOutputLowerBound.construct_sigma`. The returned Selection P is attached to that same S, retaining its exact original chosen samples, fibers, output support and index provenance.

For the actual sigma=2^(P.level)*delta and Q equal to the cardinality of the actual output support, the theorem gives

`lambda^2/(512*outputConstant) < sigma ≤ fiberCoefficient/kappa`,

`Q ≥ (outputCoefficient/16) kappa^(5(k+1)) lambda^6 I^2 / (sigma^2 delta^2 pivotLog(delta)^3 E)`.

The ambient space is k+2 throughout. The factor 1/16 is exactly 1/8 from the existing output theorem multiplied by 1/2 from the marked angle count.

## Literal manuscript minimum

`construct_source` specializes the arbitrary-radius theorem to

`kappa = c_w min{theta, 1/100, (c_w/B)^(1/alpha)}`,

where `c_w=1/[100(2width+1)]`, B≥1, alpha>0 and theta>0. Its actual full-family two-ends premise has coefficient **2B**, matching the post-pruning coefficient. All the scalar tests are discharged by `MinPivotKappa.source_admissible`. Its remaining collision condition is explicitly in this same minimum radius, and the returned sample system and selection literally carry it as their parameter.

The specialization neither replaces the source minimum by the smaller product nor requires logarithmic budgets on B or theta. It therefore closes the actual marked-sample/output-selection bridge for the source convention. Original spatial pruning/recovery and the downstream simultaneous slab/closing package still need new generic-radius wrappers to instantiate this theorem; the frozen original package retains its product definition.

## Verification

Both theorems clean-compile. A fresh full-source audit passed with an exact source-prefix match, no errors or warnings, and axiom union exactly `propext`, `Classical.choice`, `Quot.sound`. The dependency `.olean` is built and the module is frozen. No new axioms or admitted steps were introduced.
