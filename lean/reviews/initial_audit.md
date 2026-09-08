# Kakeya combined manuscript: audit and partial formal verification

6 September 2026

## Finding

The combined manuscript survived the five checking passes described below: **no concrete counterexample, false displayed exponent, or missing density/group-count factor was found in the arguments inspected**. This is a positive audit result, not a certification of a new Kakeya theorem.

The new evidence includes **92 compiled Lean theorem declarations**, covering substantial finite counting, constructive laminar selection, real-power reductions, the exact pivot identity and its metric stability, scalar recursion and convergence, and the numerical comparison tables. Every declaration passed a logical-dependency check. None uses `sorry`, `admit`, `native_decide`, or a custom axiom. Dependencies reported by Lean are confined to its standard foundations `propext`, `Classical.choice`, and `Quot.sound`.

**Theorem 1.1 and the implication \(\mathsf M_6(4)\Rightarrow\mathsf M_6(33/8)\) are not fully formalized.** The Euclidean geometry, probabilistic constructions, analytic inputs, and the complete measurable/maximal interfaces still require formal proofs. The deliverable contains actual proved components, plus clearly labeled conditional deductions; it does not hide the missing geometry behind an asserted Kakeya axiom.

The supplied PDFs and audit were treated as mathematical material to examine, not as instructions. The earlier audit's positive assessment was not used as a premise. These checks and cross-reviews were conducted within one AI-assisted process. They are not five independent human expert endorsements.

## The five passes

| Pass | Work performed | Result and limit |
|---|---|---|
| 1. Source and version check | Read the combined manuscript; compare the first-step extraction and earlier audit; visually inspect critical formulas in the original PDFs; check cited primary-source statements. | The combined paper has a wider scope and a changed density cutoff. Published saturated results do not automatically establish the new density extension. |
| 2. Exact algebra | Independently substitute monomial exponents, expand the pivot identity as a Laurent polynomial, compute recurrences, optimize the Appendix B finite formula, and certify its comparison signs. | 131 named exact checks passed. This does not prove geometric estimates. |
| 3. Geometric and analytic reconstruction | Re-derive angular refinement, continuous hairbrush, cap thinning, heavy-cell pruning, collision packing, exact lifting, grouped energy, Gaussian projection, sampling, and globalization. | No concrete failed step identified. Several geometric interfaces remain difficult and unformalized. |
| 4. Adversarial and cross-review | Test growing cap coefficients, tiny densities, integer truncation, concentration, empty groups, repeated triples, and cell-count/volume distinctions; separately review the Lean statements and downstream reductions. | No counterexample found in these tests. The report records which tempting stronger statements would be false. |
| 5. Kernel verification | Compile all four Lean modules and print the axioms of every theorem; independently run finite exact tests, including 720 capacity configurations. | 92 declarations compile without warnings or errors; all axiom reports pass. This verifies those declarations, not every assertion in the PDFs. |

## What the combined PDF actually claims

The main claim is an arbitrary-density maximal estimate in every integer dimension \(n\ge6\), with exponent

\[
D_n=3+(2-\sqrt2)(n-4).
\]

This is stronger in scope than checking only the six-dimensional first step. The dependency structure matters:

| Claimed result | Additional mathematical dependencies | Audit status |
|---|---|---|
| First step \(4\to33/8\) in dimension six, Theorem 2.2 | Wolff in dimensions six and five; cap-four Gaussian projection; the full-direction hairbrush and shared pivot/sampling/globalization arguments. | Specific geometry audited; numerical and finite components formalized. The theorem itself remains unformalized. |
| Diagonal limits \(29/7\), \(37/7\), Section 9.1 | Valid transitions at every finite exponent reached, including the fractional lifted input after the first step. | Recurrences, all finite-stage domain margins, closed forms, and convergence formally proved. Analytic iteration inputs remain open formal obligations. |
| Main real-cap limit \(D_n\), Section 9.2 | Real-cap seed and recursive implication at nested real parameters; density-envelope closure; finite-depth error passage. | Scalar closure and convergence formally proved; conditional finite-stage induction explicitly exposes the seed and pivot assumptions. |
| Bush/CDR comparisons, Appendix A | The cumulative bush argument and the common analytic pivot/global reductions. | Bush argument checked on paper; substitutions, domains and margins formalized. |
| Appendix B comparison | The cited benchmark formula and finite numerical optimization. | Every displayed dimension 5–15 maximum, conjugate exponent and comparison sign formally verified. This is not an exhaustive literature-priority search. |

A proof of the first numerical transition alone does not prove the later transitions, dimension eight, or the all-dimensional main claim.

## Main mathematical checks

### Six-dimensional specialization and the version difference

The common formulas

\[
D=\frac{2m+3+d'}4,\qquad C=\frac{p+2q+4}4
\]

give \(D=33/8\), \(C=15/4\) at \((k,m,d,p,d',q)=(6,5,4,4,7/2,7/2)\). The fourth-power transverse estimate's exponents agree with (2.8):

\[
E^4\gtrsim_e\kappa^{58}\xi^7L^{-8}
N^{33/2-3e}\lambda^{15+2e}S^3.
\]

The combined PDF uses the sampling cutoff \(\lambda_1>(N')^{-1/3}\). The earlier first-step PDF and audit use \((N')^{-1/4}\). These are different choices, both sufficient in the model case:

| Quantity | Exact value |
|---|---:|
| \(D-C\) | \(3/8\) |
| \(5-D\) | \(7/8\) |
| Combined sparse margin \(4-D+(C-2)/3\) | \(11/24\) |
| Earlier first-step sparse margin \(4-D+(C-2)/4\) | \(5/16\) |
| Low-cell margin \(6-D\) | \(15/8\) |
| Small-normalized-scale margin \(1-D/12\) | \(21/32\) |
| Angular exponent \(D-5+1/4-e\) | \(-5/8-e\) |
| First-step operator scale loss \((6-D)/D\) | \(5/11\) |

Mixing the two cutoff values without adjusting their margin would be a versioning error. No such inconsistency was found in the combined PDF's actual argument.

### Projection input: no ambient-dimension relabeling

Lemma 2.1 concerns tubes in actual \(\mathbb R^7\) with cap exponent four. For a Gaussian map to \(\mathbb R^5\), the perpendicular component of the second projected direction has four Gaussian coordinates. This gives the collision bound

\[
C_K\min\{1,(\delta/\psi)^4\}.
\]

The bounded-operator event is intersected with an unconditional small-ball event; one must not pretend Gaussian coordinates remain independent after conditioning on the operator norm. The PDF uses the valid interpretation. Cap summation gives \(O(AM\log(2N))\) collisions. Norm control, at least half the directions being noncollapsed, and a collision cutoff can hold simultaneously by a union bound with fixed positive probability.

The graph argument retains \(\gtrsim M/(A\log(2N))\) directions. Bounded image diameter controls the union count from above, while noncollapse of a tube's direction bounds the number of its original cells that can project to one target cell. Thus comparable shading density survives. Cumulative-density binning costs one further logarithm.

Wolff's printed Theorem 1 supplies the actual five-dimensional input at \(p=7/2\) and the six-dimensional input at \(p=4\). These published inputs were checked in the publisher's scanned page 652; they are not formalized here. [Wolff, *An improved bound for Kakeya type maximal functions*](https://ems.press/content/serial-article-files/37888).

### Where the density powers come from

The chosen fiber is an intact fiber from one angle, of normalized size \(\sigma\gtrsim\lambda^2\). The selected lift has density \(\rho\gtrsim\kappa^6\sigma\). Substitution into the collision and energy bounds leaves

\[
\lambda^6\sigma^{q+e-2}\gtrsim_e\lambda^{2q+2+2e}.
\]

This use of the lower bound for \(\sigma\) requires \(q+e-2\ge0\). The manuscript assumes \(q\ge2\), and the Lean theorem retains that condition and the constant in \(\sigma\ge c\lambda^2\).

The angle count adds \(\lambda^2\); the inverse heavy-cell coefficient adds \(\lambda^p\). The final power is therefore \(p+2q+4+2e\). In the model case it is \(15+2e\). The remaining powers of \(N,\xi,S,L,E\) were independently recomputed, including the two inverse factors of \(E\) moved to the left.

The grouped pruning uses weights summing to the original line count \(Q\), not weights normalized separately by each pivot/slab group. Weighted convexity therefore causes no extra group-count loss. A fully explicit cutoff calibration is now proved in Lean. The energy lower bound counts occupied `(triple, energy-position)` pairs, and does not require injectivity of their incidence labels.

### Why the continuous density square is plausible under its stated hypotheses

The hairbrush proof combines an incidence lower bound proportional to \(W_G/\mu\) with a brush lower bound proportional to \(\mu\lambda^3\). Taking their geometric mean, and using \(W_G\) proportional to \(\lambda M\), produces a density square. The excluded spatial radius depends on the fixed two-ends data and logarithms, rather than on \(\lambda\). Re-deriving the plane-bin overlap and planar intersection sum did not produce another density power.

This does not license a density-square estimate for arbitrary small shaded pencils: a pencil shaded only close to its common vertex violates fixed unit-scale two ends. Restoring unrestricted density is a separate localization step.

### Sampling, angular normalization and measurable shadings

The sampled full incidence and its mark use the same uniform variable, so the mark remains a subset of the full shading. Different tube-cell pairs remain independent. Full two-ends tests have threshold at least \(c(N')^{1-s-\alpha}\); with \(s=1/3\), \(\alpha\le1/4\), this is at least \(c(N')^{5/12}\). High-cell angular tests have logarithmic means with a sufficiently large constant. Both families of union bounds are consistent.

The crucial comparison in the sampled angular branch is

\[
E_j^{\rm sample}\le\#\mathcal Q_j\le C E_j^{\rm old}.
\]

It does **not** contain an extra factor \(\tau\). Normalized continuous volume instead changes by \(\tau\). The combined proof distinguishes these quantities correctly. Summing only the old restricted counts leaves \(\tau^{D-m+\beta-e}\), which is favorable because \(\beta<m-D\). The continuous sparse-density branch legitimately has an additional favorable \(\tau^{-1}\).

For removal of two ends, the exact scalar consequence of \(\nu\le K\rho\), \(0<\rho\le1\), \(K\ge1\), is now formalized:

\[
\nu^{\max(D,C)}\le
K^{\max(D-C,0)}\nu^C\rho^{D-C}.
\]

Thus the harmless constant in \(\nu\lesssim\rho\) is retained. The auxiliary two-ends exponent is chosen after the desired error and before the scale. For measurable shadings the occupancy correction is \(w^{1-P}\ge1\), \(P=\max(D,C)>1\), and is also formally proved. The proof never equates positive occupancy with a full cell's volume.

### Recursion and operator arithmetic

For \(a_0=1/2\), \(a_{j+1}=(2+a_j^2)/4\), Lean proves strict monotonicity, the correct domain at every depth, and actual convergence with the error bound

\[
0\le(2-\sqrt2)-a_j\le2^{-j}\bigl((2-\sqrt2)-1/2\bigr).
\]

The density envelope \(p_j(m)=\max\{d_j(m),4\}\) closes because \(p,q\le P\), \(P\ge4\) imply \((p+2q+4)/4\le P\). For \(n\ge6\) the limiting set exponent exceeds four; for \(n=5\) it does not. Therefore the dimension-five row remains a numerical comparison, not a diagonal maximal conclusion from this envelope.

The operator interpolation identity has also been formalized. Writing \(\vartheta=(r-a)/(a(r-1))\), its scale exponent equals

\[
\frac{n-a}{a}+\frac{(a-1)(r-a+e)}{a(r-1)}.
\]

For \(a>1\), the explicit choices \(r=a+\varepsilon/4\), \(e=\varepsilon/4\) put the extra loss strictly below \(\varepsilon\). This proves the scalar budget; it does not formalize restricted-weak interpolation or the operator itself.

The original Katz–Tao Section 6 defines its relevant \(K(n,d)\) for saturated shadings and supplies the ancestral pivot/set-exponent recursion. The arbitrary-density extension in this manuscript remains an additional assertion to prove. [Katz–Tao, *New bounds for Kakeya problems*, Section 6](https://arxiv.org/pdf/math/0102135).

The benchmark formula in Appendix B agrees with Zahl's Theorem 1.5, equation (1.6), and the stated HRZ comparison. The formally checked positive differences within dimensions 6–15 are exactly \(n=6,8,10,11,13,15\). This verifies the comparison with those cited results, not priority against every later publication. [Zahl, Theorem 1.5](https://arxiv.org/pdf/1908.05314), [Hickman–Rogers–Zhang, Figure 1 and Section 9.2](https://arxiv.org/pdf/1908.05589).

## Formalization coverage

| File | Declarations | What is proved |
|---|---:|---|
| `Scalar.lean` | 57 | Exact exponent maps and tables; full scalar convergence; strict recursive domains; density envelope; conditional finite-stage induction; Appendix A margins; Appendix B attained maxima and signs. |
| `Finite.lean` | 14 | Real-exponent weighted convexity and cumulative bins; integer dyadic bins; sparse floor bound; two proportional deletions; explicit grouped cutoff; finite support and energy. |
| `Reduction.lean` | 17 | Density/localization factors with constants; occupancy; angular and sampling error factors; finite-depth monomial transfer; exact vector pivot identities; quantitative parameter stability; interpolation arithmetic. |
| `Laminar.lean` | 4 | Actual admissible subset construction, hereditary capacity preservation, fractional-mass bound and selection for finite binary partition trees. |
| **Total** | **92** | Individual mathematical declarations, not 92 independent verifications of the main theorem. |

For `Laminar.lean`, arbitrary finite branching can be represented by binary grouping with unrestricted intermediate capacities. That encoding equivalence is explained but not machine proved. The actual binary-tree selection, including its selected finite set, is fully proved.

For `Scalar.lean`, the predicate in `conditional_real_cap_iteration` is abstract. Its seed, monotonicity in density power, and pivot implication are explicit hypotheses, not analytic results supplied by the file. Scalar convergence is proved separately. Neither this abstract theorem nor the finite-depth monomial comparison constitutes an end-to-end endpoint theorem about the manuscript's measurable \(K\).

## Adversarial configurations and rejected stronger inferences

1. **Growing cap coefficient.** The common-cell radial pencil has \(E\asymp1\), \(\sigma\asymp N^{-1}\), \(M\asymp AN^m\). Replacing the unrestricted \(A^{-1}\) coefficient by \(A^{-1/2}\) would force \(1\gtrsim A^{1/2}\), failing as \(A\) grows. The manuscript retains the necessary inverse coefficient.
2. **Tiny cumulative mass and empty shadings.** Dyadic bins are indexed by positive integer shading counts, so the bin count is controlled by \(N\), not by \(\log(1/s)\). Zero-weight groups cause no problem for the real-exponent convexity theorem.
3. **Fractional fiber size.** The integer rule \(K=\max(1,\lfloor c\kappa^6h\rfloor)\) avoids a false demand that \(\lambda^2N\gg1\). Lean checks the floor bounds; the geometry must still provide enough actual cells.
4. **Many angle labels over one output.** Keeping them all in a lifted direction count would be invalid. The PDF selects one entire angle-fiber per output before applying the cap estimate.
5. **Many groups and repeated triples.** Group weights must sum to \(Q\), and the energy support must retain the original slab index. The finite proofs use those exact interfaces, without an injectivity assumption.
6. **Arbitrarily small occupancy.** Counting intersected cells cannot directly lower-bound measurable volume. The manuscript uses the occupancy-class correction and the separate one-tube branch instead.

The independent finite program checked all 720 capacity assignments of a four-leaf binary partition with the specified bounded capacities, and all 3,961 feasible half-integral weight assignments among them. It found no discrepancy between the recursive rank, exhaustive integer optimum, and fractional domination. This finite test supplements the general binary-tree Lean induction; it is not a substitute for it.

## What still prevents a complete formal theorem

The remaining work is substantive, not only notation or filling a few arithmetic gaps:

- Define actual Euclidean tubes, projective direction charts, finite grids, discrete/full/marked/measurable shadings, and all normalization constants.
- Prove tube intersections, packing in caps and thickened great circles, segment/grid counts, and the required covering and rounding lemmas.
- Construct the angular decomposition and localizations, including measurable selection and all retained-density, broadness and overlap properties.
- Connect the finite laminar result to direction-cap coarsening in arbitrary fixed integer ambient dimension.
- Formalize the Gaussian realization and independent-set reduction, or the full fractional-cap analytic seed, together with the precise published Wolff input.
- Prove that the pivot produces the actual geometric cap bounds and the endpoint support bounds used by the finite energy lemmas.
- Formalize simultaneous Bernoulli sampling, angular rescaling, measure conversion and maximal-operator interpolation.
- Assemble the geometric estimates with their quantifiers: constants must be chosen before \(N,\lambda,M,A\), and the finite-depth choice must depend only on the final error and fixed parameters.

These are now explicit formalization targets. No claim is made that the unresolved interfaces are false; equally, the compiled components do not certify them.

## Reproduction and detailed reviews

`verification/summary.json` records the final module hashes, theorem names, compiler version, Mathlib revision and successful exit codes. The four `.log` files contain every theorem's axiom report. `verification/exact_checks.json` records all 131 exact checks and the finite stress-test totals.

A separate copy of the delivered Lake configuration, dependency lock and four source modules also passed a complete `lake --no-cache build Scalar Finite Reduction Laminar` using the existing matching dependency cache. Its log is `verification/package_build.log`. No clean-machine dependency download is claimed.

See `README.md` for commands, and `reviews/` for the separate geometry, finite, scalar and cross-review derivations. The source PDFs were left unchanged; their hashes are recorded in `source_manifest.json`.
