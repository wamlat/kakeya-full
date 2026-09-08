# Exact measurable density trimming

`MeasurableDensityTrimming.lean` is frozen, clean-built with zero diagnostics, and its production `.olean` is available. SHA256: `5a93da1d10e71880ebb326e6dd06f14640b205a39c6ba1c488661ec473e02d66`.

## Actual construction

For every bounded measurable Y in Space(n+1) and every 0≤a≤volume.real(Y), `exists_exact_subset` constructs a measurable literal subset Z⊆Y of finite volume exactly a. The proof pushes restricted Euclidean volume under the norm map. Every radial fiber is an actual sphere of Lebesgue measure zero, giving continuous cumulative radial mass. A containing closed ball and the intermediate value theorem produce the required radial cut Y∩closedBall(0,r). No grid approximation, supplied mass-selection oracle, or external axiom is used. The positive ambient dimension is explicit: the claim is not made for the atomic Space(0).

`construct F Y hY hsub ha0 hle` returns `Nonempty (Output F Y radius a)` simultaneously for the original finite family. Each original Y_i is bounded by its actual compact tube carrier, so no common bounded-position hypothesis is required. The output keeps the original F and original indices literally, and contains:

- measurable shadings Z_i⊆Y_i⊆carrier_i(radius), finite volume and exact volume a;
- containment of the new actual union in the same original union, including the corresponding real-volume inequality;
- exact sum_i volume.real(Z_i)=M*a, including M=0;
- `two_ends_ratio`: each old radius test transfers with coefficient B*volume.real(Y_i)/a for a>0;
- `two_ends_upper`: with a common upper mass U, B≥0 and r≥0, every old test transfers with coefficient B*U/a.

Since F is unchanged, original direction separation, cap bounds and base geometry need no new preservation premise. No broadness survival under arbitrary trimming is asserted. The later fixed/logarithmic density substitution and its constants are deliberately left to the separate continuous seed assembly.

## Validation

Clean command: `lake env lean -o .lake/build/lib/lean/MeasurableDensityTrimming.olean MeasurableDensityTrimming.lean`.

Full exact-source audit: `MeasurableDensityTrimming_full_source_audit.lean/.log/.json`. PASS for all 10 named declarations (9 theorems and one output record); source prefix and SHA verified; dependencies use only `propext`, `Classical.choice`, and `Quot.sound`. No custom axiom, `sorry`, or warning. The geometry agent independently reviewed the actual mathematical construction without finding a defect.

Only this new module and its reports/audits were edited; no frozen source or shared registry was changed.
