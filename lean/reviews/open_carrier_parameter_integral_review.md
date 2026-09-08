# Separate review of open carriers and parameter integrals

Read-only mathematical review of the frozen `TubeOpenCarrier.lean` and `ParameterLIntegral.lean` found no substantive defect.

The closed and open carriers are literally the segment plus the corresponding Euclidean closed/open radius ball, with the original parameter interval [0,1]. For positive radius, closure of the open carrier is the entire closed carrier: each closed-ball witness is approximated by the same-center open ball. Convexity then supplies a proved Haar-null frontier, and the closed/open discrepancy lies on that frontier. The resulting a.e. equality is an equality of actual sets, so restricted measures and nonnegative set integrals agree for arbitrary integrands; no integrability or measurable-integrand assumption is needed merely to replace an a.e.-equal domain. The positive-radius condition is correctly retained in this replacement.

Joint openness in base/direction is proved directly as a union over the actual axis parameters of strict continuous-distance sublevel sets. The direction variable need not be normalized for this auxiliary statement, which correctly allows later restriction to the sphere subtype.

The parameter-integral lemma uses nonnegative ENNReal-valued integrands, measurable spatial sections and pointwise lower semicontinuity in the parameter. Pointwise values are bounded by their parameter-filter liminf; monotonicity of the nonnegative integral followed by the proved Fatou inequality supplies the lower-semicontinuity bound. First-countable parameter topology is explicit, as needed for the invoked filter form. It does not assume domination, finite integrals or joint measurability. The open-set section lemma uses the actual indicator of an open parameter-membership set; a nonnegative constant, including infinity, gives a lower semicontinuous indicator. Spatial measurability follows from measurable f and measurable sections.

The final open-tube integral is jointly lower semicontinuous in the original base and direction for measurable nonnegative f. These modules alone do not claim the supremum is measurable: the remaining composition requires restricting direction to the actual sphere, using the separately proved fixed positive carrier denominator, and taking the all-base supremum. Those are valid separate downstream steps rather than hidden hypotheses here.

This is a statement/proof review, separate from the producer's compilation and full-source axiom audit.

Reviewed SHA-256 values:

- `TubeOpenCarrier.lean`: `293bdfaa6917d7477e25a62aee70c07e6cc81323718a8b7ab14c73abd133810a`

- `ParameterLIntegral.lean`: `1f87ef795080fcf9c5cc0b04a61c8a659fc894d6494ed4b71cd07bb70e56a8f7`
