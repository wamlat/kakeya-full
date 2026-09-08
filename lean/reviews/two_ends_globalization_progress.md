# Actual removal of two ends

`TwoEndsGlobalization.lean` is clean-built and frozen. Public theorem:

```
TwoEndsGlobalization.remove_two_ends
  (hestimate : TwoEndsDiscreteEstimate (k+1) m D C)
  (hm : 0 ≤ m) (hD : 1 ≤ D) (hC : 1 ≤ C) :
  DiscreteEstimate (k+1) m D (max D C)
```

This is an unrestricted estimate on the actual `ShadedConfiguration` predicate. The caller supplies no two-ends property, localization, partition, population budget or local estimate. Each fixed geometric normalization and epsilon precedes the final constant, which precedes every actual configuration and its scale, density, cap coefficient and population.

The proof chooses the localization exponent and local scale error before invoking the given two-ends estimate. At a fixed small-mesh cutoff, actual admissibility gives unit-ball coverage about the tube midpoint. Actual common-radius and common-density selection supplies relative two ends, density at least rho^alpha times original density, and population at least a fixed constant times log(2/delta)^(-2) times original population. Local tube counting derives the upper density bound proportional to rho. `LocalizedTwoEndsApplication.localized_bound` internally constructs the spatial bins and all normalized estimates, sums their old disjoint unions, and retains the single original inverse-cap factor. Scalar globalization absorbs the radius and density loss, then a second uniform log absorption absorbs the actual two class-depth losses. The empty family and all remaining mesh scales are handled explicitly.

Five exact-source named declarations (one definition, four theorems) compiled and passed a fresh appended `#print axioms` audit with only `propext`, `Classical.choice`, `Quot.sound`. No new or external axioms, sorry or admit. SHA-256: `fca72eb28ade95cc8b17912eb5fee7a7637efcc765aaf6ed75476c51557f69b2`.

Audit artifacts: `TwoEndsGlobalization.full_source_audit.lean`, `.log`, and `.audit_metadata.json` in audit_work. Root independently reviewed the final theorem and reported no defect. An independent read-only review of the three actual local partition/normalization/application modules is saved as `localized_partition_independent_review.md`.

This closes the remaining full-two-ends hypothesis for the actual discrete all-angle pivot interface. The six-dimensional numerical specialization and the general recursive endpoint are assembled in separate modules; measurable extension retains the precise measurable predicate's own ambient and geometric hypotheses.
