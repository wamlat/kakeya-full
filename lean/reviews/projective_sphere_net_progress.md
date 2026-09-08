# Entire projective-sphere net

`ProjectiveSphereNet.lean` is a new source outside the frozen 381-module checkpoint 21. It imports the previously proved `CapCover`/`ProjectiveGeometry` chain. Its production `.olean` builds with zero diagnostics.

The main public result is `KakeyaFormal.ProjectiveSphereNet.exists_indexed_net`. For ambient dimension `k+1` and `0 < rho <= 1`, it constructs a natural number `M` and actual vectors `center : Fin M → Space (k+1)` satisfying all of the following simultaneously:

- Every center has norm one.
- Distinct centers have projective chord distance at least `rho`.
- `M <= packingConstant k * (1/rho)^k`, with exactly the existing packing constant and no additional radius or dimension factor.
- Every unit vector in the entire ambient space lies at projective distance strictly less than `rho` from some center.
- Every closed projective `rho`-cap centered at any unit vector is contained in one of the actual open `2*rho`-caps centered at this same indexed net.

The record `Net k rho` and `exists_net` expose the underlying finite set with its unit, separation, cover and cardinality fields. `Net.center`, `center_unit`, `center_separated`, `center_covers` and `center_double_cap` expose the actual enumeration. `Net.cap_containment` also proves the general closed radius-`r` to open radius-`rho+r` containment, without assuming that a tested vector is unit.

## Construction and semantic checks

The actual projective packing theorem bounds every finite separated set of unit vectors. For this use only, the auxiliary packing-cap center is zero: every unit vector has projective distance exactly one from zero. The constructed net centers themselves are all unit vectors.

The set of realizable natural cardinalities is bounded by the ceiling of that real packing bound and contains zero. `Nat.findGreatest` selects a largest realizable cardinality. If any unit vector were uncovered, it could be inserted while preserving separation, creating a strictly larger realizable cardinality. This proves coverage of the whole sphere rather than only an input finite family. The exact real cardinality estimate is then reapplied to the constructed set, so the natural ceiling does not inflate the final constant.

The cap-containment proof uses the strict covering inequality plus the genuine projective triangle inequality. It therefore handles closed original caps while producing open double-radius tests, including caps whose centers do not occur among the input tubes. No covering, maximality, compactness or cardinality estimate is supplied as a desired-result premise. Dimension `k=0` is allowed and does not require a special positivity assumption beyond the ambient dimension `k+1`.

## Source coverage and remaining work

This closes the geometric net ingredient of the paper's display (6.19): a net of the *entire* projective sphere with the actual ambient-minus-one cardinality exponent. It does not itself create the modified finite-product sampling tests or prove the source's separate failure probabilities. Those remaining steps are to integrate the original raw marked broadness over these net masks, combine the support count with the inverse-log bound on `rho`, absorb the polylogarithmic net count into the source polynomial at a uniform threshold, and derive the literal `<1/8` and joint `>3/4` probability displays.

The already proved sampling existence theorem used original tube directions as test centers. This new full-sphere net must be explicitly substituted into the test construction before claiming that its smaller cardinality is the cardinality of that earlier test family.

The production source hash is `9417c061c19cb7675e20474f1aab27e2d46a63ce10fcd5d295bc273beb5308ef`. The exact-source dependency audit is recorded in `projective_sphere_net_audit.json` and `ProjectiveSphereNet_axioms.log`. No frozen source, shared registry, verifier or lakefile was edited.
