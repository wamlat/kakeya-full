# Actual localized application of the two-ends estimate

`LocalizedTwoEndsApplication.lean` is frozen and clean-built. Its two source theorems and all nine local theorem declarations passed an exact complete-source dependency audit, using only `propext`, `Classical.choice`, and `Quot.sound`. Source SHA-256: `f94be66373842f91d597b4459789be71fcd1df6cf01053043ce78adbd656f21e`.

`localized_bound` fixes the dimension, original width, positive two-ends exponent, coefficient B≥1, nonnegative cap and density powers, positive scale loss, and a concrete `TwoEndsDiscreteEstimate` BEFORE choosing a positive estimate constant. For every subsequent actual localized comparable family, it proves

`c A⁻¹ δ^(m−D+eta) s^C rho^(D−C) M ≤ card(original union)`.

The family must have positive population, 0<δ≤rho≤1, positive comparable density s, A≥1, actual original tube admissibility and cap bounds, per-tube localization centers, and relative two ends for δ≤r≤rho. No original separation or bounded-base assumption is needed: the actual cap thinning and spatial partition supply the normalized hypotheses internally. No output configuration, density, count, common-origin, or spatial-summation oracle is assumed.

The proof constructs the old-cell `Partition`, then its actual normalized outputs in every occupied bin. Each normalized configuration has fixed geometry, cap coefficient `capConstant`, scale δ/(K rho), density `Partition.density`/(K rho), and a fixed two-ends coefficient `(2 binCount B) K^alpha`. The normalized estimate constant is chosen before δ, rho, s, A, population, bins and families. The proved population sum retains rho^m/(retentionConstant A); the normalized union cardinalities sum into the disjoint ORIGINAL unions.

The exact arbitrary-density scaling identity gives rho^(D−C−eta). Since rho≤1 and eta>0, the claimed rho^(D−C) term is smaller. The retained density is at least s/binCount; C≥0 therefore costs only the fixed factor binCount^C. There is exactly one inverse original cap coefficient and no additional radius or logarithmic loss.

This discharges the actual geometric localized estimate corresponding to §8 equation (8.1). It is not itself the unrestricted theorem: selecting the original common localization scale/density, absorbing population logarithms and the final measurable conversion remain in downstream modules. The imported two-ends estimate is a literal explicit premise, not an axiom.

Evidence: `localized_two_ends_application_axioms.lean`, `localized_two_ends_application_axioms.log`, and `localized_two_ends_application_audit.json`. Independent geometric review is being recorded separately.
