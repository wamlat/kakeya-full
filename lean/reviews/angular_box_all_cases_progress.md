# All local angular cases on actual boxes

`AngularBoxAllCases.lean` is complete: three theorems, a clean `.olean` build with zero compiler diagnostics, and exact-source axiom audit artifacts. It combines the already proved bounded-normalized-scale, coarse angular, low-density hairbrush, and high-density sampled-pivot estimates on the SAME actual `AngularSpatialSampling.Package U`.

## Final theorem

`construct` fixes a positive c before F, both scales, angular pieces P, refinement V, simultaneous package U, good box q, original density, cap coefficient, and populations. It proves

`c*A^(-1)*(δ/P.tau)^(m-pivotSet(m,d')+ε)*physicalDensity(V,width)^(pivotDensity(p,q))*originalBoxPopulation ≤ #refinedCells`.

No branch cutoff, sparse/high density condition, quantitative log budget, separate sampling Input, marked-mass bound, population bound, or desired old-cell lower bound occurs in this final statement. The supplied Package is the actual previously constructed one; the proof uses its SAME output for the density split.

The explicit fixed analytic inputs remain `DiscreteEstimate (k+2) m d pExp` and `DiscreteEstimate (k+3) d d' qExp`. The numerical range is m≥1, m+1≤ambient, pExp≥1, d≥0, qExp≥2, pivotSet<m+1, positive alpha/beta/epsilon, original B≥1 and R≥0, the positive sparse margin, and the fixed width-power test. The density exponent is derived to be at least two from pExp and qExp. Original actual-family admissibility, separation, bounded bases and cap control are required, along with positive original mesh, original density≤1, actual angular-group membership, and original natural log≥1.

## Uniform case assembly

The coarse exponent is fixed to `a=2*ambient`. Before introducing any configuration, the proof chooses:

1. the high-density threshold δh and positive cH;
2. the actual bounded-normalized-scale coefficient cB at that fixed δh;
3. the actual coarse-angle coefficient cC;
4. the actual low-density coefficient cL.

The final c is `min(min(cH,cB),min(cC,cL))`, whose positivity is proved. All decreases in the coefficient are justified by a proved nonnegative common target factor.

For the actual normalized mesh s=δ/P.tau, the exhaustive split is:

- If s≥δh, use the bounded-scale bound from one original full shading and actual cap population.
- Otherwise, if δ^(1/a)≤s, use the actual coarse angular bound.
- In the complement, `fine_power_comparison` proves the literal scale condition s^a≤δ by real-power monotonicity, including the exact reciprocal exponent identity.
- If the SAME output density is at most s^(1/3), use the constructed low-density hairbrush bound in original physical density and population.
- Otherwise use the high-density estimate. `inverse_density_cutoff` proves exactly `(1/s)^(-1/3)=s^(1/3)`, so the low/high cutoff conventions leave neither a gap nor an unhandled equality case.

Every branch has precisely the same original physical-density power, original box population, inverse original cap factor, and literal old-cell count. No normalized-volume expression is substituted for an old count.

## Remaining scope

This is the full LOCAL case theorem, not yet the global angular summation. That summation additionally needs the stronger global range pivotSet<m and a choice beta<m-pivotSet, plus the already proved original-cell overlap and retained density/population budgets. The original log≥1 and fixed width normalization remain honest outer conditions; the global theorem must arrange them and handle any remaining bounded original-scale range.

No new custom axiom, `sorry`, `admit`, or assumed analytic conclusion is introduced. The generic analytic base/lift estimates are ordinary explicit hypotheses. Existing exact published axioms, where authorized elsewhere, are not imported as additional premises here.

Source SHA-256: `e4b8b483dcbf82507ff155137c6d37545118458e0452702023707cb4be7f2279`.

Audit artifacts: `AngularBoxAllCasesSourceAudit.lean` and `audit_work/AngularBoxAllCases_axioms.log`. The finite agent independently reviewed the statement/case split and found no mathematical issue before the final audit; a final-byte review report is being completed separately.
