# LogarithmicTwoEndsAlgebra

Final source `formalization/LogarithmicTwoEndsAlgebra.lean`, SHA-256 `8497459fb6230c4df07a5afb8c013722d3bf68867803385c4d614bddb6c4342e`. Clean Lean compile and production .olean with zero diagnostics. Production whole-source audit `LogarithmicTwoEndsAlgebra_operator_audit.json` PASS: 3 named theorems, 10 local theorem declarations, 11 total local declarations; dependencies only `propext`, `Classical.choice`, `Quot.sound`. No sorry, custom axioms or unproved analytic predicate. The source is outside frozen418 and shared registry/verifier files were not edited.

The exact coefficient is `lossPower beta C D = max 0 (beta*C+D-C)/beta`. With beta>0,C≥0,rho∈(0,1],lambda>0,B0>0,L>0, actual density lower `rho^beta*lambda≤s` and actual radius constraint `1≤2*(B0*L^b)*rho^beta`, `density_factor` proves

`(2*B0)^(-lossPower)*L^(-(b*lossPower))*lambda^C ≤ s^C*rho^(D-C)`.

This preserves C, including when D−C+beta*C is negative. The proof raises the actual constraint to nonnegative q=lossPower, factors strictly positive real powers, and uses rho≤1 to replace the max exponent by the desired exponent in the correct direction. It needs no b≥0 premise; later source budgets use that additional condition. There is no independently assumed lower radius bound by a root.

The public geometric/analytic consumer remains separate: it must derive both supplied scalar inequalities from the SAME actual localized rows and the original logarithmic two-ends hypothesis, obtain the local estimate, account for population, and absorb the final explicit log. Scalar agent owns that new LogarithmicTwoEnds module. Thus this algebra theorem is not itself a proof of the first-step Lemma6 extension.

Scalar independently read the complete final source and reported no issue with the max exponent, signs or positive-base identities. Its final hash-specific review may be recorded separately by that agent.
