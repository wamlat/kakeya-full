# Cross-review of Lean statements and downstream reductions

6 September 2026. This review was carried out separately from authoring `Reduction.lean` and `Finite.lean`. It is a second AI-assisted review pass, not independent human certification. I read the full source of both files and freshly read the combined PDF's Sections 6–8, physical pages 25–32. I did not edit either Lean file.

## Result

No material statement mismatch, custom axiom, tautological replacement for a disputed geometric conclusion, contradictory specialization, or sign error was found in these two Lean files. No concrete failure of the PDF's sampling/globalization arguments was identified in the fresh read. The machine-checked scope remains substantially narrower than the final Kakeya theorem, as the file headers correctly state.

## Reduction.lean: statement-to-manuscript mapping

The final file has seventeen named theorems (the original thirteen plus four additions reviewed below). The real-power hypotheses are explicit and mathematically sufficient.

| Lean result | Manuscript step | Assessment and exact limit |
|---|---|---|
| `localized_density_gain` | (8.1), p.31 | Correct normalized scalar inequality for `0<nu<=rho<=1`; the PDF has `nu<=C_0 rho`. Applying the lemma to `nu/C_0` returns a fixed factor `C_0^(C-max(D,C))`. Thus the exact hypothesis is stronger only by an explicitly manageable normalization. The theorem does not construct a localization. |
| `occupancy_factor`, `occupancy_gain` | Measurable passage, p.32 | Correct for `0<w<=1`, `P>=1`. The lower bound on the number of occupied cubes and their selected occupancy class is still geometric/measurable input. |
| `angular_factor` | Angular summation, p.29 | Correct direction: because `tau<=1`, exponent `D-m+beta-e<=0` makes the factor at least one. `beta<=m-D` and `e>=0` are sufficient; the paper uses a strict margin. |
| `density_error_absorption` | Sampled high-density branch, p.30 | Correct for real `s,e`, with `e>=0` and `lambda>=N^(-s)`. Positive `lambda` follows from the displayed lower bound and `N>0`. |
| `fiber_density_gain` | Lemma 5.2, p.24 | Correctly uses `q>=2` so the power of `sigma` is nonnegative. The constant `c` is retained as `c^(q+e-2)`; no hidden assumption `c=1`. |
| `finite_depth_transfer` | Limit passage, Section 9 | Correct conditional monomial comparison once finite-depth exponent and density bounds are available. It does not by itself establish convergence or uniform analytic constants. |
| `choose_two_ends_exponent` | Choice of alpha, p.31 | Supplies an actual positive alpha bounded by one quarter with the required error margin. |
| `small_density_one_tube` | First paragraph p.32 | Correct for `lambda<=delta`, `P>=1`, `D<=P`; the tube-volume and family-cardinality estimates that turn it into a one-tube comparison remain outside the statement. |
| `pivot_convex_identity` | Pivot segment identity, p.23 | Proves the exact vector identity with nonzero denominator. Despite the convenient name, it does not assert that the coefficients are positive or that the point belongs to a segment. Positivity is supplied in the PDF by legal samples, and must not be claimed as proved by this theorem. |
| `pivot_defect_identity` | Identity preceding (5.31), p.23 | Correct exact vector identity with nonzero `b,u_*`. It does not prove that rounding errors are `O(delta)` or establish lower geometric separation. |
| `parameter_stability`, `parameter_interval_length` | Parameter recovery after (5.31), p.23 | Correct norm inequalities; positive `A` is explicitly needed for the division in the interval theorem. Substitution `A=c kappa^3`, `B=C kappa^(-2) delta` yields the stated interval scale. Packing the resulting interval into grid cells is still unformalized. |

The pair of exact vector identities is not a formal substitute for the quantitative Euclidean hypotheses. The statements and comments respect this distinction. No `axiom`, `sorry`, `admit`, or unsafe declaration was found in the source inspected.

## Finite.lean: statement-to-manuscript mapping

The file has fourteen named theorems. They prove actual inequalities about finite sums, not a theorem with a new Kakeya estimate hidden as an assumption under a different name.

| Lean result(s) | Manuscript step | Assessment and exact limit |
|---|---|---|
| `weighted_power` | (5.27), p.23 | Real-exponent weighted convexity, permitting zero weights. Normalization is by total weight `Q`, so it proves the absence of a factor depending on the number of groups. |
| `cumulative_from_bins` | Corollary 1.1, pp.3–4 | Correct finite-bin consequence with exactly `bins.card` in the loss. It uses an incidence-weighted mean at least `rho`; dyadic lower endpoints require the usual fixed-factor adjustment. It does not itself assemble tube shadings into bins. |
| `dyadic_bin_membership` | Logarithmic bin count | Actual integer bin membership and index bound, valid for every positive count `n<=B`; does not depend on cumulative density being at least `1/N`. |
| `nonempty_floor_truncation` | (5.22), p.21 | Correct lower and upper bounds on `max(1,floor x)`, including `x<1`. Existence of enough actual cells to select that number remains separate geometric input. |
| `proportional_bad_mass`, `proportional_good_mass` | (3.8)–(3.9), p.10 | Correct finite deletion inequalities with the actual threshold. The assumptions are weaker than nonnegative incidence data, which is harmless; they are not contradictory or vacuous in the application. |
| `retain_good_pieces`, `restoration_constants` | (3.10), p.10 | Correct second deletion estimate and stated `3/4`, `5/8` constants. The first theorem uses the actual pointwise threshold, rather than assuming its conclusion. |
| `grouped_cutoff_retains_half` | (5.27)–(5.29), p.23 | Conditional on per-color analytic lower bounds and the actual high-cell upper bound, it proves that deleted incidence mass is below half the original mass. Those hypotheses are exactly the two distinct inputs in the paper. They are openly labeled and are not themselves formalized here. |
| `cutoff_calibration_identity` | (5.26), p.22 | Exact real-power cutoff identity; for positive geometric parameters its factor-two margin supplies the strict calibration. The main cutoff lemma also assumes calibration explicitly. |
| `bounded_multiplicity_energy` | Energy upper bound in (5.29), p.23 | Correct nonnegative multiplicity inequality. |
| `support_card_by_fibers` | Support counting preceding (5.32), p.24 | Correct finite counting-by-fibers lemma. The uniform geometric per-triple support bound is explicit input. |
| `finite_support_energy` | (5.32), p.24 | Correct Cauchy–Schwarz and aggregation argument. Labels must represent occupied `(triple,energy-position)` pairs, not incidences individually. Its hypothesis is on the cardinality of these pair labels; the source comments state exactly this. Taking `beta` to be the finite set of actual energy positions meets the `Fintype` requirement. |
| `close_energy` | Passage to (5.33), p.24 | Correct positive-incidence cancellation. It concludes `I_0<=2 C N H E^2` from the displayed lower/upper energy and retained-mass inputs. Substituting the geometric powers is a separate calculation. |

No source-level custom axiom, `sorry`, `admit`, or unsafe declaration was found. Some lemmas allow zero/negative values beyond the intended nonnegative application; this makes their domains wider, rather than making the positive specialization vacuous. The `hcalibrate` hypothesis in grouped pruning is satisfiable with positive parameters, as its explicit cutoff identity demonstrates. No unnoticed dependence on group count, nonzero weight for every group, or integer exponent was introduced.

## Fresh check of Sections 6–8

### Sampling: physical pp.25–27

The use of the same uniform variable for full incidence and its mark preserves the subset relation, while different tube-cell pairs remain independent. The mean full shading count is exactly `h^(-k)|F_T|`, so comparable density at the threshold `lambda>N^(-s)` gives a polynomially large mean `N^(1-s)`. Ball tests use cell centers and a fixed enlargement, so no assumption below scale `h` is needed.

The full two-ends upper-tail threshold is at least `c N^(1-s-alpha)`. The declared strict inequality `alpha<1-s` makes this grow polynomially and dominates the `O(N^(2k-1) log N)` tests. The high-cell broadness tests instead need only means of size `a_0 log N`. Integrating pointwise broadness gives the required expectation bound on every direction-net cap. The numeric estimate

`(e/50)^(mu/20) <= exp(-mu/8)`

is in the correct direction because `(log 50-1)/20 > 1/8`. Choosing `a_0=64(k+4)` makes the polynomial union bound ample. The proof does not require independent failure events; the union bound suffices.

Output cells can extend beyond the measurable union, but (6.11) promises only containment in its grid-cell support. The downstream proof uses this weaker property correctly.

### Angular globalization: physical pp.28–30

The all-angle proof distinguishes old restricted grid-cell counts from transformed volume and from sampled coarse-grid counts. In the high-cell branch it uses only `E_sample<=#Q<=C E_old`. It does not wrongly recover the extra `tau^(-1)` volume factor from a sampled cell count. Consequently the angular exponent is `D-m+beta-e`, requiring `D<m`, as explicitly stated. The small-density branch can use continuous hairbrush volume and does have the additional favorable `tau^(-1)`.

The four branches cover the intended parameter range. The normalized-small-scale branch uses one old tube and `D<k`; the sparse-density branch has positive margin `(C-2)/3-(D-w)`; the high-cell branch uses `s=1/3` and `alpha<=1/4`, so the full two-ends threshold grows at least as `N'^(5/12)`; and the low-cell branch gets its union bound directly from deterministic expected marked mass. Its ratio to the target contains the positive power `N'^(m+1-D)` and the favorable factor `lambda^(1-C)`. I found no omitted density factor in these comparisons.

### Removal of two ends and measurable conversion: physical pp.30–32

The localization has `nu>=c L^(-A) rho^alpha lambda` and `nu<=C rho`. Cap-preserving coarsening pays `rho^m`, not the larger actual ambient exponent. Isotropic rescaling preserves cell counts and yields `nu^C rho^(D-C)`. The sign case split for `P=max(D,C)` is correct; the auxiliary alpha is chosen after the final error budget and before scale, avoiding a varying-alpha constant problem.

The measurable occupancy argument uses the occupancy of the entire measurable union in each cell. Removing very-low-occupancy cells costs at most a controlled fraction of each tube's shading since a tube meets `O(N)` cells. A common occupancy class and per-tube mass class retain inverse-logarithmic mass and tube count. A selected cell's occupancy upper bound gives a lower bound on discrete density, and its occupancy lower bound converts selected cube count back to original union volume. The resulting factor `w^(1-P)` is favorable for `P>1`. At no point is positive occupancy alone identified with full cell volume.

## Remaining conclusion

The reviewed Lean files substantiate their advertised finite, scalar, and vector statements. They do not formally derive all their hypotheses from Euclidean tubes. The paper's Sections 6–8 also survived this particular fresh read, but their probability, covering, geometric-rescaling, and measure-conversion arguments remain mathematical audits rather than complete machine formalizations. No result of this cross-review warrants calling the final unrestricted maximal theorem machine-verified.


## Final four additions to Reduction.lean

The final `Reduction.lean` contains seventeen theorems, and the two reviewed files therefore contain thirty-one theorems in total. I inspected the four additions after the initial review. No material problem was found.

- `localized_density_gain_with_constant` directly handles the actual hypothesis `nu<=K rho`, with `K>=1`, `0<nu`, and `0<rho<=1`. Its conclusion pays exactly `K^max(D-C,0)` on the right. If `C<=D` this is the needed `K^(D-C)` factor; if `C>D` the factor is one. This closes the scalar normalization interface noted for the earlier normalized theorem. Existence of the geometric localization is still outside the formalization.
- `interpolation_weight` proves the identity `1/a=(1-theta)/r+theta`, with `theta=(r-a)/(a(r-1))` and all denominators explicitly nonzero. This is the arithmetic in Section 9.3, physical p.34. The general identity does not assert `0<=theta<=1`; in the intended specialization this follows from `1<a<r`.
- `interpolation_loss_identity` proves the exact decomposition of the interpolated scale loss as `(n-a)/a+(a-1)(r-a+e)/(a(r-1))`. It matches the expression on physical pp.34–35 and does not use an operator bound as a hidden premise.
- `interpolation_loss_budget` assumes `a>1`, `eps>0` and supplies actual witnesses `r=a+eps/4`, `e=eps/4` with `r>a`, `e>0`, and total loss less than `(n-a)/a+eps`. The remainder is bounded by `r-a+e=eps/2`, giving the strict margin. No sign or quantifier mismatch was found. This proves the scalar parameter choice, not the analytic restricted-weak or strong interpolation theorems.

These four additions contain no custom axiom, `sorry`, `admit`, or unsafe declaration in the source inspected. Compilation of the final seventeen-theorem file is part of the parent task's final validation; this supplementary pass checks statement correspondence and proof scope rather than claiming a separate compilation run.
