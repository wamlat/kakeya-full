# Separate geometry audit of the combined manuscript

Date: 6 September 2026. Scope: Sections 3–5, physical PDF pages 7–24 of `kakeya_combined (1).pdf`. The source documents were treated as mathematical assertions to check, not instructions. This report concerns the stated arguments; it is not a certification of the unrestricted final theorem.

## Finding and method

I found no concrete false geometric counting inequality or missing shading-density power in the portions of Sections 3–5 checked here. This is a bounded positive audit result. In particular, it does not constitute a machine verification of Euclidean tube geometry, measurability, probability, or the final unrestricted Kakeya estimate. The parts still requiring formal proof are listed below.

The checks used five distinct methods: (1) definition and quantifier tracing; (2) direct re-derivation of geometric counts; (3) separate algebra and density bookkeeping; (4) degenerate/sparse configuration and growing-cap-coefficient stress checks; and (5) direct comparison with the original Katz–Tao argument. These methods are different tests performed in one AI-assisted process, not five independent expert endorsements. Relevant displayed formulas were also inspected in rendered original PDF pages, including physical pages 15 and 23, to avoid extraction ambiguity.

## 1. Localization and angular refinement: pp. 8–10

### Lemma 3.1 and (3.1): validated on paper

Let `r_T` be the smallest admissible dyadic radius with a ball carrying at least `r_T^alpha` of the original shading. For `r < r_T/2`, minimality bounds every radius-`r` ball by a fixed multiple of `r^alpha |Y(T)|`, while the selected shading has mass at least `r_T^alpha |Y(T)|`. Dividing gives the stated relative two-ends estimate. The upper bound `nu <= C rho` follows from the longitudinal geometry of a tube. The radius and retained-density selections each have only `O(log N)` classes: the retained density ranges between a fixed multiple of `N^(-alpha) lambda` and `lambda`, even for an arbitrarily tiny measurable `lambda`. The ball-to-cube restriction loses only a fixed factor and consequently changes the relative two-ends constant by only a fixed factor.

Formal obligation: define the finite grid/shading conventions precisely, prove the longitudinal cell count, and implement a measurable/tie-broken choice of the localizing ball. The manuscript provides a mathematical selection argument, not a formal implementation of these choices.

### Lemma 3.2: the global assignments do preserve a usable broad subset

The potentially delicate point is the assignment of each whole tube to one global direction cap, because that assignment can destroy broadness at a point. The proportional-point restriction repairs it with the stated constant loss. If the pre-assignment mass is `W`, each tube appears in at most `C` candidate caps, and the best-cap assignment retains mass `W_a >= W/C`, then deleting points where the assigned multiplicity is below `1/(4C)` of the former multiplicity deletes at most `W/(4C) <= W_a/4`. On all remaining points, the old broadness inequality is multiplied by at most `4C`. The same argument works for the spatial covering assignment.

The overlap `O(tau^(-beta))` comes from the count of pointwise selected direction subsets, not from an assertion that all enlarged angular caps are disjoint. Each selected subset has at least `c tau^beta |V|` directions, and the subsets are disjoint. Assignments only remove incidences, so the overlap cannot increase beyond the bounded spatial covering multiplicity. Thus there is no hidden ambient power `tau^(-(k-1))` in this step.

Formal obligation: a finite representation of the pointwise greedy construction, the global cap-cover multiplicity, and the parallel spatial tube cover. For unbounded tube positions the parallel covering also requires bounded-overlap longitudinal translates; the standing bounded-region reduction supplies the equivalent fixed-region version. This is an implementation detail to state explicitly in a complete formal development, not a demonstrated failure of the lemma.

### Equations (3.5)–(3.10): deletion bookkeeping is sound

Let `D` be the removed incidence mass. Outside the new good set, the surviving multiplicity is at most the lost multiplicity, so the surviving bad mass `R` is at most `D`. Hence total good mass is at least `W-2D`; discarding pieces whose good fraction is below one half loses at most another `R`, leaving at least `W-3D`. This gives the displayed `5W/8` when `D <= W/8`. The pointwise broadness constant doubles on the good set. Crucially, the full surviving shading remains available for density/two-ends, while marks impose broadness; these are not interchangeable objects.

## 2. Continuous hairbrush and real-cap seed: pp. 11–16

### Equations (4.8)–(4.15): the density square is supported by the argument

The chosen multiplicity class has mass at least `c W_G/L`, giving `|U| >= c W_G/(L mu)`. Stem transversality, together with the intersection bound `|T cap T'| <= C delta^k/psi`, gives at least `c mu lambda theta/(delta L)` bristles. The retained bristle shading after the spatial exclusion has volume at least `c lambda delta^(k-1)/L`.

For the plane bins, a point at distance `s` from the stem lies in at most `C s^(-(k-2))` planks: in the projective sphere parametrizing planes, the allowed cap has radius `C delta/s`, and the net spacing is `delta`. In a fixed bin, directions lie in a `C delta` neighborhood of a great circle, so there are at most `C psi/delta` directions in a radius-`psi` cap. The annular intersection sum is therefore `O(L delta^(k-1))` per bristle. Cauchy–Schwarz yields (4.14), and summing yields

`|U| >= c (r_0 theta)^(k-2) theta mu lambda^3 delta^(k-2)/L^4`.

Taking the geometric mean with the first incidence estimate produces (4.8). Since `W_G` itself carries one factor of the density, the comparable-density version has density power two. No additional density enters `r_0`: it is selected using the full two-ends condition and the logarithmic retained fraction, not the absolute amount of shading.

Stress check: a shading confined to a small ball around a pencil vertex does not contradict this estimate because its unit two-ends constant must grow. Thus the hairbrush estimate with fixed/logarithmic two-ends data cannot be tested by dropping that hypothesis on a concentrated pencil.

### Equations (4.16)–(4.23): normalization and cap dependence are consistent

The passage from the square-root marked-mass bound to a linear bound uses only

`W_G <= C Lambda delta^(k-1) M <= C Lambda A delta^(k-1-m)`.

It gives precisely the coefficient `A^(-1/2) delta^((m-1)/2) lambda^(3/2) Lambda^(-1/2)` multiplying `W_G`. Under transverse dilation by `tau^(-1)`, the union volume and incidence volume have the same Jacobian, so that Jacobian cancels in their ratio. The remaining angular factor is `tau^(-(m-1)/2)`. After summing with overlap `tau^(-beta)`, it is favorable exactly when `beta < (m-1)/2`, as required by (4.18).

The cap exponent remains `m` in (4.19) because the direction chart is uniformly bi-Lipschitz after normalizing an original `tau` cap. Merely knowing separated directions would not suffice when `m<k-1`; the manuscript does use the full cap hypothesis.

### Lemma 4.2 and (4.24)–(4.25): deterministic thinning is a valid integrality argument

The recursive capacity `R_v = min(b_v, sum R_child)` is an integer. A child union has `sum R_child` elements, so deleting to `R_v` preserves all upper capacities. For a feasible fractional weighting, induction gives its subtree mass `W_v <= R_v`. Therefore the selected root set has at least the fractional total mass. This argument does not require `m` to be an integer.

For the geometric application, terminal cube capacity is exactly one. Uniform weights `c A^(-1) (N r_*)^(-m)` satisfy every dyadic capacity by the original cap condition and `floor(x) >= x/2` for `x>=1`. Coloring terminal cubes enforces `r_*` separation. A ball meets only boundedly many dyadic cubes of comparable side, proving the entire cap estimate at the new scale, not merely pairwise separation. This justifies Corollary 4.4, which is needed by the pruning step in Section 5.

### Equations (4.26)–(4.29): the single inverse coefficient is necessary and is tracked

The displayed `rho >= c sigma^(1/(1-a))` in the original page 15 was visually checked. Rescaling leaves normalized cell volume unchanged under isotropic dilation. Applying the absolute-cap hairbrush after thinning yields

`E >= c L^(-P) A^(-1) N^((3-m)/2) sigma_1^2 rho^((m-1)/2) M`.

With `q=(m+3)/2`, substitute `sigma_1 >= c rho^a sigma` and `rho >= c sigma^(1/(1-a))`. The exponent is exactly

`2 + (q-2+2a)/(1-a) = q/(1-a)`.

The growing-`A` pencil on page 16 checks an essential sharpness constraint: an unrestricted replacement by `A^(-1/2)` is false. The stated thinning pays `A^(-1)` once, and the hairbrush input thereafter has an absolute coefficient. This is the correct logical order.

## 3. Pivot pruning and finite output counts: pp. 17–21

### Equations (5.6)–(5.10): no circular pruning bound found

The base estimate supplies `E >= c_e N^(d-e) lambda^p S`, hence `F >= C_e c_e N^e (L/xi)^(p+1) >= 1` after its constant is enlarged. If one scale of heavy cubes carried too much incidence mass, at least `c a M` tubes would each encounter at least `c a lambda/r` such cubes. Corollary 4.4 keeps `c a M/(Nr)^m` tubes with the full coarse cap condition. Applying the base estimate at scale `r` forces (5.8). Multiplying by the disjoint heavy-cube lower bound and substituting `F` produces a factor `N^(2e) r^e >= N^e`, contradicting the chosen large constant. There is no need to assume that all original tubes survive later in the argument: (5.10) follows from surviving marked mass, while `M,S,E` remain original comparison values.

Formal obligation: establish coarse-shading admissibility including rounding when the lower cardinality is below one. The text addresses the nonempty/trim case, but this is a real interface to implement in a formal proof.

### Equations (5.11)–(5.14): fiber selection respects small densities

The full two-ends condition gives fixed positive mass portions separated by `kappa`, producing `c lambda^3 N^3` legal triples per angle. For fixed angle and intermediate label there are `O(N)` rounded pivots, hence `O(lambda N^2)` outputs. A fixed output fixes the intermediate coordinate; solving its pivot constraint restricts one endpoint to an interval `O(delta/kappa)`, giving at most `C kappa^(-1) N` pairs per fiber. The retained integer dyadic fiber size `h>=1` therefore gives

`sigma=h/N >= c lambda^2`, and `|Omega| >= c lambda^3 sigma^(-1) N^2 |A|/L`.

These deductions remain valid when `lambda^2 N<1`; they do not require a fictitious nonempty fiber of fractional cardinality.

### Equations (5.15)–(5.19): collision packing uses actual ambient dimension

For fixed output, the second tube direction is determined to `O(delta kappa^(-2))`; ambient direction separation gives `O(kappa^(-2(k-1)))` possibilities. Selecting its most frequent value keeps whole angle-output edges and their fibers.

For fixed angle and a colliding output, the competing first direction lies within `C delta/kappa` of the original two-plane. In a shell of radius `phi`, tangential packing gives `O(N phi)` possibilities and normal packing costs `O(kappa^(-(k-2)))`. Each competing first tube gives `O(1/phi)` intermediate labels, each such label gives `O(N)` rounded pivots, and the competing vertex contributes `O(kappa^(-1))` labels. The product is `O(kappa^(-(k-1)) N^2)` per shell. This also bounds the shell below `delta` by using `phi=delta`.

Cauchy–Schwarz then yields precisely the `kappa^(5(k-1)) lambda^6 sigma^(-2) N^2 |A| L^(-3)` output count in (5.19). Selecting one angle per distinct output is legitimate because every surviving edge has a fiber of at least `h` pairs; no division by the number of angles over an output is needed.

## 4. Exact lifts and energy: pp. 21–24

### Equations (5.20)–(5.25): exact graph lines and distinct output labels are essential

The manuscript fixes one pivot coefficient `u_*` per output before defining a graph line. The other pivots in that selected fiber differ by `O(delta)`, giving a common exact line carrying their lifted second endpoints. The loss of at most `C kappa^(-4)` pairs per lifted cell follows by differentiating/rationally comparing `b=a_0 c/(c-u)` and using `|c-u|>=c kappa^2`. Splitting the `t` range into `O(kappa^(-1))` unit slabs yields enough cells for the common integer `K=max(1,floor(c kappa^6 h))`.

The output `(z_0,i_0)` is unique, so for a fixed `z_0` the relation `v_f=bar(z_0)-bar(i_0)+O(delta)` implies bounded multiplicity at the direction-separation scale and the real-`d` cap bound `C F(Nr)^d`. This would fail if angle multiplicity were retained over a single output, but the preceding selection removes it. Unit-slab translations do not hide `kappa`-dependent tube length or bounded-region constants: graph slopes are uniformly bounded, and the selected horizontal endpoint is in the original bounded region.

### Equations (5.26)–(5.29): grouped pruning does not pay for the number of groups

For deleted incidences in every original group/color, the lifted estimate must apply to arbitrary cumulative density, including empty shadings. With this hypothesis, weighted convexity gives

`sum M_gc s_gc^(q+e) >= Q (I_high/(NQ))^(q+e)`.

The weights sum to `Q` regardless of how many groups exist. The high-cell upper bound is at most `J_0 I_high/H_cut`. Comparing these expressions rules out `I_high >= I_0/2` with exactly the displayed cutoff. This is conditional on the analytic input (5.5) with uniform linear inverse cap coefficient; citing only a comparable-density theorem would leave a gap, but the manuscript explicitly derives the needed cumulative version.

### Equations (5.30)–(5.33): endpoint support and energy are consistent

The pivot is on the endpoint segment with positive coefficients, so a fixed ordered pair of endpoint labels admits only `O(N)` pivot cells. For `t=c/u_*`, direct re-derivation gives

`t z - y_2 - (t-1)y_1 = (u-u_*)[-(b/u_*)u_1+t u_2]`.

The residual is `O(kappa^(-2) delta)`. The distance `|bar(z_0)-bar(e_1)| >= c kappa^3` implies that a fixed triple has all possible `t` values in an interval of length `O(kappa^(-5) delta)`. Its horizontal lift coordinate lies within `O(delta)` of its fixed second endpoint, so the triple occupies only `O(kappa^(-5))`, hence `O(kappa^(-6))`, energy positions. The group label is included because the triple fixes `z_0` and the original lifted cell fixes the slab.

Cauchy–Schwarz may be applied to triple/energy-position multiplicities without any injectivity assertion. At a fixed energy position, the sum of their squares is bounded by the square of the total incidence multiplicity. This proves the finite-support deduction (5.32) once the geometric support bound has been established. Combining the lower energy bound with `Ecal <= H_cut I` and `I>=rho NQ/2` gives (5.33).

### Lemma 5.2 and (5.3): density accounting has the stated monotonicity condition

The relevant product is `lambda^6 sigma^(q+e-2)`. Since `q>=2`, replacing `sigma` by its lower bound `c lambda^2` is in the correct direction and gives `lambda^(2q+2+2e)`. The angle count contributes `lambda^2`; `F^(-1)` contributes `lambda^p`. Thus the final fourth-power exponent is `p+2q+4+2e`. The condition `q>=2` is essential for this proof and is stated. There is no justification here for dropping it.

## 5. Comparison with primary source and remaining scope

The original Katz–Tao paper, Section 6, physical pages 19–24, defines `K(n,d)` for saturated shadings, and proves the pivot/lift mechanism in that setting. Its Theorem 6.2 has the same set-exponent transformation after writing `m=n-1`. The combined manuscript follows the original collision and lifting geometry but adds explicit finite-density pruning, integer fiber selection, exact-line rounding, and grouped cumulative-density estimates. These are substantive additional assertions. The old paper supports the lineage and the saturated mechanism; it does not by itself prove the arbitrary-density extension. Source: [Katz–Tao, New bounds for Kakeya problems](https://arxiv.org/pdf/math/0102135), Section 6.

A complete machine proof still needs Euclidean tube-intersection bounds, quantitative projective packing, finite coverings and angular normalization, choice and measurability of refinements, the analytic base/lift input interfaces, and the downstream sampling/measurable-globalization arguments. The finite lemmas and arithmetic can be proved separately, but checking them must not be advertised as a formal proof of these geometric inputs or of the main maximal theorem.

The appropriately scoped conclusion is that the inspected Section 3–5 geometry survived these particular adversarial checks, with the geometric/formal interfaces above still open to further verification. No concrete counterexample, hidden additional density loss, or fatal error was established in this audit.

## 6. Completed machine formalization from this audit

`outputs/kakeya_verification/Laminar.lean` now kernel-checks a constructive finite form of Lemma 4.2. It defines an actual binary partition tree with finite element sets and integer node capacities, requires disjoint supports of siblings, and proves four results:

1. `admissible_mono`: deleting selected elements preserves all descendant capacities.
2. `attainsRank`: an actual finite subset attains the recursively computed integer rank.
3. `mass_le_rank`: every feasible fractional weighting with individual weights at most one has total mass at most that integer rank.
4. `fractionalSelection`: a feasible weighting in `[0,1]` admits an actual selected subset with cardinality at least its total fractional mass, satisfying all node capacities.

The proof uses induction, disjoint finite-set unions, and finite-set truncation; it does not assume laminar integrality as an axiom. The binary-tree theorem is fully proved. A general finite-arity rooted partition can be represented by grouping siblings with added grouping capacities equal to their support cardinalities; that representation equivalence is explained in the file but is not itself formalized. The geometric direction-chart construction and cap-cover consequences (4.24)–(4.25) remain outside this Lean theorem.

Validation: Lean 4.33.1 with mathlib commit `0df444a360eaa60ab8c11dca51a86af692955474`. The final file compiled successfully with exit status zero and no warnings. Printed axioms for `attainsRank` and `fractionalSelection` are only `propext`, `Classical.choice`, and `Quot.sound`; no `sorryAx` appears. The compile command used the existing mathlib project's `lake env lean` with the source file at its absolute path; no source was written into that existing project.
