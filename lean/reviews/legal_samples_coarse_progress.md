# Actual legal samples and coarse-scale closure

The new root-owned modules contain 15 source theorem/lemma declarations:
`LegalParameterSelection` (7), `LegalTubeSamples` (4), and `CoarseBounds` (4).
Individual compiles are clean; the delivered checkpoint manifest records the
separate full build and axiom audit.

## Actual legal abundance, combined PDF (5.11)

`LegalParameterSelection.finite_quantile` selects an occupied parameter, rather
than assuming an order-statistics interface. Physical interval nonconcentration
then gives an orientation and actual early/late subsets, each with at least one
eighth of the first shading's labels. Their coordinates are separated from the
vertex and from each other by kappa. At least half of the second shading lies
outside the vertex interval. The actual Cartesian product therefore has at
least density^3/128 original ordered label triples.

`LegalTubeSamples` defines the coordinates by genuine orthogonal projection.
If both a cell center and the common vertex belong to a width*delta tube, the
projection to the parallel axis through that vertex has error at most
2*width*delta, and coordinate absolute value at most 1+2*width*delta.
The theorem `legal_triples_from_tubes` derives the one-dimensional interval
bounds from the original physical ball two-ends tests. It constructs at least
(lambda/delta)^3/128 actual legal triples with bounded coordinates.

The precise small-scale inputs are delta <= kappa,
(2*width+1)*kappa <= 1, and
B*((2*width+1)*kappa)^alpha <= 1/16. The shadings each have at least
lambda/delta labels, and the actual common vertex lies in both tubes.
This is the longitudinal abundance step only. Selection of enough transverse
angles, global calibration of kappa, output-count bounds and collision assembly
remain separate statements. This theorem does not assume or prove angle
transversality merely from common incidence.

## Coarse scales

`CoarseBounds.coarse_configuration_bound` uses an actual nonempty shading and
the real-cap total-count bound to control every configuration with delta >= a.
For any target m,d and p >= 1 it gives the target bound with the explicit
positive constant

    1 / [packingConstant(k) * max(1, a^(1-d+epsilon))].

The empty-family case is handled too. `DiscreteEstimate.of_small_scales`
therefore reduces the full estimate to delta <= a, provided a>0 and its estimate
constant are chosen before each configuration. The threshold cannot depend on
the later scale, density, cap coefficient, family or tube count.

No custom axioms, admissions, unsafe proofs or external numerical oracles were
introduced. The new statements do not prove the full pivot or unrestricted seed.
