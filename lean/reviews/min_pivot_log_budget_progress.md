# Sharp source minimum logarithmic budget

MinPivotLogBudget.lean clean compiles and passes the exact-source all-declaration audit. SHA256: a80c585e5f7be68da70e8e27f78d6cfdbc0a5973d697a40cf192050c69c4e8e8. There are 7 local theorem declarations and 8 all-local declarations, using only propext, Classical.choice and Quot.sound. It is outside frozen checkpoint20; independent review passes; see min_pivot_log_budget_geometry_review.md.

The actual generic minimum c*min(theta,1/100,(c/B)^(1/alpha)) satisfies the literal section5.8 lower bound with exponent A*max(1,1/alpha). Its explicit positive prefactor is c*min(theta0,1/100,(c/B0)^(1/alpha)), which is independent of A, B, theta, N. It depends only on the fixed geometric c, B0, theta0 and alpha. Assumptions are A>=0, B>0, alpha>0, L>=1, B<=B0*L^A and theta>=theta0*L^(-A).

The concentration branch follows by monotonicity in B and the exact real-power identity; the angular and constant branches follow by exponent monotonicity. The maximum replaces the earlier sufficient product bound's sum of losses. source_lower instantiates the original source minimum; normalized_lower retains the fixed normalization factor inside both appearances of the geometric constant. source_log_ge_one proves N>=2 implies log(2N)>=1 from exp(1)<3, so no A-dependent logarithmic-floor constant is introduced. source_notation quantifies the positive prefactor before every A, B, theta and N.

This closes the sharp minimum-log display itself. It does not claim the separate original Gaussian projection argument, exact alternate retention fractions, or literal original net-test count have been reproduced.
