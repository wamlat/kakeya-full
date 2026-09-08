# Independent statement review: actual angular/spatial summation

Read-only review of `AngularSpatialSummation.lean`, including both `cancel_logarithmic_overlap` and `from_piece_estimates`, against the literal outputs of AngularSpatialSampling, AngularSpatialBudgets.total_population, AngularRefinementBudgets.density_budget, AngularSeedPieces.pruning, the original-grid overlap theorem, and combined PDF §7. No shared source was edited.

No mathematical defect was found. The manuscript's logarithmic and angular-scale accounting is represented by explicit inequalities with the correct directions.

The all-box population budget is truly derived. The original retained angular groups contribute one inverse logarithm: their summed population is at least `(3/2)*P.eta*M`. The actual refinement contributes two inverse logarithms, and the subsequent good spatial-box selection contributes one. Thus `total_population` has power L^-4, with constant `boxPopulationCoefficient*(3*etaCoefficient/2)`. It sums every actual good spatial box, rather than choosing one box and losing a transverse population factor.

The physical density lower bound is `cD*L^-1*lambda`, where `cD=etaCoefficient/[2*W^ambient]` and W is the original fixed width normalization. This accounts for the common homothety exactly once. Different angular groups may have different actual refinement densities; monotonicity with C>=0 permits replacement by this uniform lower bound. There is no assumption of a globally chosen common density class.

Combining density to power C with all-box population gives exactly L^-(C+4). The positive log-loss constant is chosen before every scale/configuration and absorbs this into delta^loss. The original cap coefficient A remains A^-1; there is no constant depending on A, M, density, or a particular angular group.

The old-cell sum is bounded by `2*Csp*tau^(-beta)*E_original`, using the same actual refined old cell unions. No normalized volume identity or overlap hypothesis for sampled cells appears. Since 0<tau<=1 and beta<=s, the elementary angular inequality is `delta^s <= tau^beta*(delta/tau)^s`. Multiplication by tau^beta cancels the old overlap exactly, leaving the correct final exponent delta^(s+loss). This agrees with the sampled route's source factor tau^(D-m+beta-eps).

The scalar cancellation lemma does not separately require E>=0; its displayed estimate already forces that when needed, and multiplying/cancelling uses positive factors. Likewise the M=0 case presents no division by population. All powers used in multiplicative identities have positive bases.

`from_piece_estimates` chooses its constant before F, scales, lambda/A, Pieces P, refinements V and SpatialData T. Its only analytic interface is visibly an estimate with a single fixed cPiece for EVERY literal good box on those same objects. It derives density, total population and old-grid overlap instead of taking them as hypotheses. The theorem remains CONDITIONAL on those per-box estimates; it is not itself an unrestricted pivot estimate. The next actual-constructor/all-cases assembly must discharge that interface, and the condition L=log(2/delta)>=1 still needs its stated scale treatment. For the expected application s=m-D+eps_piece and beta<m-D, beta<=s follows with the favorable sign.

Reviewed SHA-256: `6cbd10d28d2ba103973bd734b0863260555edab2d72f9871dca0d547e1d88d7a`. This report does not duplicate the parent's full-source compilation/axiom audit.
