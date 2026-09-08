# Constructed grouped high-cell pruning

`GroupedIncidence.lean` constructs the actual high and retained finite incidence sets from the original records and their coarse group-cell labels. It proves exact mass partition and multiplicity identities, and that all retained multiplicities are bounded by the cutoff H.

Actual colored support has at most the finite number of colors times the actual coarse support. Combining this with the cutoff condition yields

`H * #coloredHighSupport ≤ #colors * #originalIncidences`.

Thus the upper estimate used in manuscript (5.28) is derived from the actual finite supports, not supplied as an overlap hypothesis. The retained energy is the actual sum of squares of group-cell multiplicities and is bounded by `H * #retainedIncidences`.

`calibrated_pruning` uses the cutoff `H=2^(r+1)*J*N/[a*rho^(r-1)]`. Its explicit substantive hypothesis is the cumulative analytic lower bound for every actual restricted incidence subset T: `a*Q*(|T|/(NQ))^r ≤ #coloredSupport(T)`. It constructs a retained subset with more than half the original mass and the proved energy upper bound. Deriving this analytic premise from concrete lifted configurations, cumulative input estimates and weighted grouping remains separate. There is no hidden bound on the number of groups.

Individual compilation and .olean construction pass cleanly. The next full checkpoint runs the isolated build and axiom inventory for all declarations.
