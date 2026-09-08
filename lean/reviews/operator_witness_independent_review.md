# Separate mathematical review of the operator core and finite witness cover

Read-only review of the frozen `KakeyaOperator.lean` and `IndicatorWitnessCover.lean` found no substantive mathematical or statement defect.

The core uses the literal closed radius-δ unit carrier. Its denominator is proved finite and strictly positive for δ>0 from the actual tube-volume theorem, before dividing. Every indicator numerator is finite even when E has infinite measure, because it is intersected with a finite carrier. The real indicator density lies in [0,1], so its supremum over all original bases is a bounded real supremum. `mem_indicatorLevel_iff` uses a strict level and `lt_ciSup_iff`; it produces an actual original tube position without assuming a supremum is attained. Clearing the denominator preserves the strict inequality because positivity is proved. General-function averages and suprema remain ENNReal-valued; the module does not incorrectly assert measurability of an arbitrary uncountable supremum.

The cover first uses compactness of the sphere subtype to cover the actual level set by finitely many ordinary chord balls with centers in that same set. Applying the proved maximal projective net to those centers gives separation δ/2 and projective cover radius strictly below δ. The center membership, projective triangle inequality and chord-to-projective comparison are explicit. This applies to an arbitrary set of directions, including a nonmeasurable or empty level set; level-set measurability is not smuggled into the compactness argument.

The final Witnesses record uses an injective Fin reindex of that actual finite net. Each index has an independently selected actual base satisfying the strict average witness. Its measurable shading is exactly E intersect the corresponding original carrier, the union is contained in E, and the actual family is δ/2-separated. Thus the forthcoming MaximalShading application must use the fixed separation parameter 1/2, rather than silently claiming δ separation. The sphere-cap upper bound can use radius δ and the same M; there is no extra direction or output multiplicity.

No desired level-set measure bound, witnessing-tube premise, attained-supremum premise, or finite-cover premise is assumed in `construct`. The remaining analytic boundary is the general operator's measurability and interpolation, not the finite witness geometry. This review does not duplicate the agents' compiler/environment audit.

Reviewed SHA-256 values:

- `KakeyaOperator.lean`: `0d8d8fc4e1bb53ed4cb8c4a9861e0eff1aa994f108f4ef27a487543d8cc3302c`

- `IndicatorWitnessCover.lean`: `581cad5dec639e3ce7e5885cc9e82c27a5e3fffeb7c21d9f1afc5133d85fa665`
