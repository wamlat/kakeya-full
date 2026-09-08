# Independent statement review of actual localized spatial normalization

Reviewed `LocalizedCellPartition.lean`, `LocalizedGroupedNormalization.lean`, and `LocalizedTwoEndsApplication.lean` read only, including their actual finite definitions and proof links. No substantive defect found.

- Every original localized tube selects an actual occupied coarse cell. Uniform integer trimming keeps all tube indices, costs a fixed `2*binCount` in two ends, and yields a common positive density at least the original localized density divided by `binCount`.
- Every retained old cell has the same coarse label as its assigned tube. Thus old unions belonging to distinct bins are disjoint. Population sums equal the original population. The proof does not assert that the independently translated new unions are disjoint; their cardinalities are bounded separately by these disjoint old unions.
- Each group's normalization uses a common snapped fine-grid origin. The axis interval is chosen from actual admissibility and localized cell geometry, with fixed dilation large enough for unit length and density at most one. No divisibility relation between the two scales is assumed.
- Actual cap thinning supplies the normalized separated family, absolute normalized cap coefficient, and retained population proportional to `rho^m/A`. Original cap dependence is paid exactly once. Each output is a literal `ShadedConfiguration` with fixed geometry, density, scale and inherited full two ends.
- The fixed normalized two-ends constant is `(2*binCount*B)*dilationConstant^alpha`; it has no dependence on mesh, radius, population or localization class depth.
- `localized_bound` applies the given uniform two-ends estimate to all actual outputs with these same fixed parameters, sums their estimates, substitutes the actual population and old-union bounds, and uses the favorable `rho^(-eta)` factor in the correct direction for `rho≤1`. Its constant precedes the actual family and every variable scale, density and cap coefficient.

The localized theorem still explicitly requires localized/comparable full shadings, relative two ends and original admissibility/cap hypotheses. These are supplied constructively by `FiniteGridLocalization` and `FiniteLocalizedFamily` in the forthcoming globalization theorem; they are not assertions of an unrestricted bound.

Reviewed SHA-256 values:

- LocalizedCellPartition: `6868d9372707681e6320130a647660569c6f5a160543d1373a6f7866084ed0a2`
- LocalizedGroupedNormalization: `86c4426e10b71fc3cb249e4c2e05ec7f42fbdafd19397dd2342ce0b91476e2dd`
- LocalizedTwoEndsApplication: `f94be66373842f91d597b4459789be71fcd1df6cf01053043ce78adbd656f21e`
