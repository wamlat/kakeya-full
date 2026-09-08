# Six-dimensional all-angle theorem under full two ends

`formalization/SixDimensionalAllAngles.lean` is complete, clean-built, and frozen. It imports `SixDimensionalCore` and `AllAnglePivot`; no registry or shared source was edited.

The single public theorem `two_ends_estimate` proves the actual finite occupied-cell lower bound

`c*A^(-1)*delta^(7/8+eps)*lambda^(15/4)*M <= card(F.unionCells)`

for every actual six-dimensional tube family at every delta in (0,1], with lambda in (0,1], A>=1, and original admissibility, delta-separated directions, bounded bases, real cap parameter five, comparable full shadings, and full two ends at every radius delta<=r<=1. The fixed two-ends coefficient has B>=1, alpha>0, and eps>0. Fixed width and base-radius parameters are allowed; the general all-angle theorem internally enlarges them by fixed constants when needed.

The positive c is chosen BEFORE the actual family, population, mesh, shading density and cap coefficient. There are no marked-set, broadness, angular decomposition, spatial box, sampling outcome, logarithmic-budget, small-scale, or local-density-branch hypotheses.

Both analytic inputs are discharged by the standard-only constructive fractional seeds already proved in SixDimensionalCore:

- actual ambient six, cap parameter five, base set/density exponents four;
- actual ambient seven, cap parameter four, lifted set/density exponents seven halves.

The exact specialization is D=(2*5+3+7/2)/4=33/8, C=(4+2*(7/2)+4)/4=15/4, m-D=7/8, and sparse margin (5+3)/2-D+(C-2)/3=11/24. The source includes the exact margin identity, and Lean normalizes the rational exponent expressions in the resulting theorem.

This is the ALL-ANGLE TWO-ENDS six-dimensional estimate. It is stronger in scope than the previous marked specialization, because every angular/marked/spatial/sampling hypothesis has now been constructed from the original full shadings. It is not yet the unrestricted M6(33/8) theorem: removing the original full two-ends hypothesis, obtaining the required diagonal density exponent through localization, and the corresponding unrestricted measurable/maximal conclusions remain separate work. The theorem itself is unconditional apart from its displayed original two-ends/geometric assumptions; it uses no published-result custom axiom and no assumed base/lift estimate.

Verification: Lean 4.33.1 clean `.olean` build, zero diagnostics. Fresh complete-source audit of the single theorem passes with exact source-prefix match and only propext, Classical.choice, Quot.sound. Audit files: `six_dimensional_all_angles_full_source_audit.lean`, `.log`, and `six_dimensional_all_angles_audit_manifest.json`. SHA-256: `2d33975996b5ab36ffe964847811547f4151d90f58745fac150d2fa9b5ec3963`.
