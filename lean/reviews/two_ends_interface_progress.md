# Concrete two-ends estimate interface and proved pivot instances

Two new modules are complete, clean-built, and frozen: `formalization/TwoEndsDiscreteEstimate.lean` and `formalization/TwoEndsPivot.lean`. No registry or shared source was edited.

The lightweight interface module imports only Configurations. `TubeFamily.FullTwoEnds F delta B alpha` is the literal finite inequality on every tube, every Euclidean center, and every radius delta<=r<=1:

`card {z in F.shade i | dist(cellCenter delta z,x)<=r} <= B*r^alpha*card(F.shade i)`.

It is a transparent definition on the actual original cell labels and full shadings, not an uninterpreted geometry predicate. `TwoEndsDiscreteEstimate n m d p` quantifies one actual Normalization, B>=1, alpha>0, and eps>0 BEFORE choosing a positive c and BEFORE every `ShadedConfiguration n geom m`. That configuration supplies its actual width-admissible tubes/cells, separation `geom.separation*delta`, bounded bases, cap condition, comparable density, and positive bounded mesh/density. The only extra configuration hypothesis is its literal FullTwoEnds property. The conclusion is the same actual union-cardinality formula as DiscreteEstimate.

The interface deliberately requires B and alpha to be fixed before the configuration. A later geometric globalization may use a proved fixed coefficient depending on dimension/width/alpha. Applying the interface with a coefficient chosen from the varying mesh would not by itself give a uniform constant; any such proposed use needs separate uniform control.

`DiscreteEstimate.to_two_ends` proves the elementary restriction of an already proved unrestricted estimate. `TwoEndsDiscreteEstimate.weaken_density` proves that increasing the density exponent weakens the estimate, using the actual configuration density in (0,1]. No shading is altered and no new analytic assumption is introduced.

The second module imports the interface, AllAngleSeparation, and SixDimensionalCore. `TwoEndsPivot.from_base_and_lift` derives the interface from the actual base and lifted DiscreteEstimate inputs under the established parameter conditions: m>=1, m+1<=ambient, p>=1, d>=0, q>=2, D<m, and the strictly positive sparse margin. It calls `AllAngleSeparation.configuration_estimate` directly, so arbitrary fixed positive separation is handled by that module's proved coloring; no new coloring is duplicated here. No marked rows, broadness, decomposition, log conditioning, selected box, or sampling input is assumed.

`TwoEndsPivot.six_dimensional` proves `TwoEndsDiscreteEstimate 6 5 (33/8) (15/4)` from the standard-only actual ambient-six and ambient-seven seeds. `six_dimensional_diagonal` weakens its density exponent to 33/8. Both STILL require original full two ends through the interface. Neither is the unrestricted DiscreteEstimate or M6(33/8) statement. These are precise hypotheses for the forthcoming geometric two-ends globalization.

Verification: both `.olean` files compile cleanly under Lean 4.33.1 with zero diagnostics. Fresh exact whole-source audits pass all seven declarations (two definitions and five theorems) using only propext, Classical.choice, Quot.sound. Per-module audit files have stems `two_ends_discrete_estimate_full_source_audit` and `two_ends_pivot_full_source_audit`, with .lean/.log files and separate audit manifests.

Source SHA-256:

- TwoEndsDiscreteEstimate.lean: `26b56051b135bb719f1addfbbd176b4fd99cce1f137285f530a73402f3dfcf11`
- TwoEndsPivot.lean: `f1139b640f719dda2828060ee80a2a3b8cb43e7889b9105ba6689fa22f8ff24e`
