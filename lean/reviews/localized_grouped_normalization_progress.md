# Actual grouped normalization for Section 8

`LocalizedGroupedNormalization.lean` is frozen and clean-built. It closes the concrete normalized-family interface needed to apply the general uniform two-ends estimate to the spatial groups constructed in `LocalizedCellPartition`.

Let n=k+1, W=max(1,width), D=dilationConstant(n,width), T=retentionConstant(k,m), and Ccap=capConstant(k,m). All these constants are explicit existing definitions fixed by dimension/width/cap exponent. The actual input mesh and localization radius satisfy 0<δ≤ρ≤1.

The generic `construct` takes a positive-population localized family of comparable old density ν>0, actual radius-ρ localization balls, original CapBound(δ,m,A), admissibility, relative two ends, and one common old-grid origin within (1+n)ρ of its localization centers. It constructs actual target-scale direction thinning and a common isotropic rescaling. Its `Output.configuration` is a literal `ShadedConfiguration` with:

- normalized mesh δ/(Dρ), in (0,1];
- normalized density ν/(Dρ), in (0,1];
- width W, separation coefficient 1, and base radius (6W+1+n)/D;
- normalized cap coefficient Ccap≥1, independent of original A;
- selected population at least Mρ^m/(T A);
- an injective map into original tube indices, unchanged directions, and each shade exactly the image of the corresponding full old shade under the injective integer-label shift by the common old-grid origin;
- all-radius relative two ends with coefficient B D^alpha.

The density upper bound is derived from actual tube-ball grid counting. It is not assumed, clipped, or achieved by changing density metadata. The interval construction keeps a starting point within 6Wρ of the localization center while extending the actual axis interval to Dρ. This supplies the genuine uniform base bound omitted in the seed-only varying-center normalization.

`partition_construct` applies this construction to every nonempty bin of the actual `Partition`. Its common origins and all retained ball tests are derived from the partition, and its comparable density is the literal retained density ν=δN. It uses fixed coefficient 2K(n)B before rescaling, where K(n)=binCount(n), so normalized full two ends has coefficient

`Bnormal = 2 K(n) B D^alpha`.

`normalized_ends_ge_one` proves Bnormal≥1 for B≥1 and alpha≥0. In the source localization application B=4^alpha, so the full coefficient is fixed before all scales and configurations, as required by `TwoEndsDiscreteEstimate`. The module directly exposes `Output.full_two_ends` in that predicate.

`construct_partition` simultaneously constructs all configurations. Its actual outputs already satisfy:

- sum of normalized populations ≥ original localized M times ρ^m/(T A);
- sum of normalized union cardinalities ≤ original localized union cardinality.

The second statement uses injective label shifts to recover each old union's cardinality, then the disjoint OLD-cell bin sum. It does not assert that the differently translated normalized unions are disjoint, and does not compare their physical volumes by an invalid common-map argument.

## Remaining downstream scope

The module constructs the geometric/finite families, densities, exact correspondence, two-ends conditions, and both summations. Applying a supplied `TwoEndsDiscreteEstimate` uniformly to these actual configurations and simplifying its powers is a separate analytic step being implemented in `LocalizedTwoEndsApplication`. The actual common localization radius/density class selection and its two logarithmic population losses are supplied by existing `FiniteGridLocalization`/`FiniteLocalizedFamily`; final uniform loss absorption and the unrestricted theorem remain downstream.

## Verification

```
lake env lean -o .lake/build/lib/lean/LocalizedGroupedNormalization.olean LocalizedGroupedNormalization.lean
lake env lean ../localized_grouped_normalization_axioms.lean
```

The full-source audit copy appends the production audit of every local declaration (including definitions, type-valued structures and generated declarations). Compilation and audit have zero diagnostics. Source scan excludes sorry, admit, custom axiom declarations, unsafe, and native_decide.

See `localized_grouped_normalization_audit.json` for exact declaration counts/hash, and `localized_grouped_normalization_axioms.lean`/`.log` for the independently checked full-source environment output. Only `propext`, `Classical.choice`, and `Quot.sound` occur. Toolchain: Lean4.33.1, mathlib `0df444a360eaa60ab8c11dca51a86af692955474`.
