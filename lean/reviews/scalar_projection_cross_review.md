# Separate cross-review: scalar formalization and Gaussian projection

## Result

No material flaw found in the requested scope. This review independently checks the statements and interpretation of `Scalar.lean` against Section 9 and Appendix B, and derives the four potentially delicate steps of Lemma 2.1. It does not certify the remainder of the geometric argument.

## Scalar.lean

- `slope`, `profile`, `envelope`, `pivotSet`, and `pivotDensity` agree exactly with equations (9.4), (1.7), and (9.5). The composition is `3+a_j²(m−3)`, and the resulting slope is `(2+a_j²)/4`.
- The strict domain theorem proves `3<d′<d<D<m` for every finite depth and every `m>3`. This is stronger than the displayed non-strict `d≤D` and is correct. The nested parameter stays strictly above three.
- `conditional_real_cap_iteration` explicitly assumes the analytic seed, density weakening, and pivot implication for an arbitrary predicate `K`. Its hypotheses do not contain a disguised contradiction or `False`; they are jointly satisfiable, for example with `K(m,d,p)` interpreted as `d≤m`. The theorem is meaningful relative finite-stage closure, but it assigns **no tube/cap/scale meaning** to `K` and does not establish those hypotheses for the PDF's analytic `K`.
- There is actual convergence, not merely a fixed-point calculation: `slope_error_bound` supplies a geometric error bound, `slope_tendsto` proves convergence to `2−√2`, and `profile_tendsto` transports it to the profiles. The affine diagonal iterations have both exact closed forms and actual `Tendsto` proofs.
- **Scope boundary:** the file does not prove an endpoint-passage theorem for the abstract analytic `K`. It proves finite-stage conditional iteration, scalar convergence, and the correct density-power inequality separately. A final theorem about the scale-loss-quantified analytic estimate still requires its definition and the finite-depth/epsilon passage. This is a limitation of coverage, not an incorrect theorem statement.
- The dimension-five boundary is handled correctly. At `m=4`, the limiting set exponent is `5−√2<4`, while the density envelope is exactly four. The file proves this and does not claim a diagonal maximal estimate there. For every real `n≥6`, it proves the limiting profile at `m=n−1` exceeds four, enabling the intended diagonal interpretation once the analytic interfaces are supplied.
- Appendix B's `benchmarkCorrect` is the exact finite maximization: it requires an attained value and an upper bound for every integer `2≤ell≤n`. All entries from dimensions 5–15 and their comparison signs match the PDF. These theorems verify the arithmetic of the displayed benchmark formula, not the cited external papers' analytic results.

## Lemma 2.1: independent derivation

### Collision power four

Write `v′=cos(ψ)v+sin(ψ)w`, with `w⊥v` and projective angle `0<ψ≤π/2`. For a standard Gaussian `5×7` matrix, `Pv` and `Pw` are independent standard five-dimensional Gaussians. Conditional on nonzero `Pv`, the perpendicular projection of `Pw` has four independent Gaussian coordinates. If `||P||≤K` and the projected projective angle is at most `Cδ`, then

`sin(ψ) |proj_(Pv)^⊥ Pw| = |proj_(Pv)^⊥ Pv′| ≤ CKδ`.

Thus the event's probability is at most `C_K min(1,(δ/ψ)^4)`. One must not condition the Gaussian distribution on `||P||≤K`; the manuscript correctly bounds the intersection by an unconditional small-ball event after conditioning only on `Pv`. The event `Pv=0` has probability zero. Projective orientation causes no difficulty because the perpendicular norm uses the sine of the angle.

A dyadic annulus of radius `r` contains at most `C A (Nr)^4` directions per fixed direction. Multiplying by collision probability `C(δ/r)^4` gives `C A` per annulus. Summing `O(log(2N))` annuli gives `C A M log(2N)` ordered collisions. Directions at distances between the fixed separation constant times `δ` and `δ` are handled by the cap bound at radius `δ`, with a fixed constant. No ambient-seven power is needed or warranted.

### Simultaneous realization

Choose the norm cutoff `K` so its failure probability is below, for example, `1/8`. Choose `c>0` so each direction has `Pr(|Pv|<c)<1/16`; Markov bounds the probability that more than `M/2` directions are bad by `1/8`. The bounded-map/at-least-half-good event then has probability at least `3/4`. A sufficiently large Markov cutoff for the collision count fails with probability below `1/4`, so all three requirements hold simultaneously with positive probability. Independence of these three events is unnecessary.

### Independent set

On the good vertices `V≥M/2`, the collision graph has `e≤C A M L` edges. The random-order argument gives an independent set of size at least

`Σ_v 1/(deg(v)+1) ≥ V²/(V+2e) ≥ c M/(A L)`.

The denominator uses `A≥1` and `L=log(2N)` bounded below for `N≥1`. It remains valid for small `M` or very large `A`. Ordered versus unordered collisions changes only a factor two.

### Shading preservation

A source grid cell has image diameter `O_K(δ)`, so it meets only a bounded number of target grid cells. This gives projected union count at most `C` times original union count. On a good tube, write a cell center as `x₀+t v+O(δ)`. If two such centers project into the same target cell, then

`|(t−t′)Pv| ≤ C_K δ`,

hence `|t−t′|≤C_(c,K)δ`. The stated tube convention allows only a fixed number of source cells in such a longitudinal interval. Thus collapse multiplicity on each good tube is bounded, preserving comparable density. Projected lengths lie in `[c,K]`; fixed subdivision/enlargement normalizes lengths and widths with fixed losses. Selecting the projection only after obtaining a comparable-density bin is important and is what the proof does.

Finally, Wolff's five-dimensional exponent `7/2` has the discrete normalization

`E′≥c N^(−1/2−eta) s^(7/2) M_selected`.

Combining this with the independent-set size and the cumulative-density binning gives two logarithms. They can be absorbed in the gap between `eta` and the desired scale loss `e`. The extra density power `e` is a legitimate weakening on `0<s≤1`; bounded larger densities are normalized at the fixed cost already stated in the PDF.

The conclusion of this review is that Lemma 2.1's projection mechanism is internally coherent at the required cap, cardinality, and density dependence. The Gaussian facts and the imported Wolff theorem have not been machine formalized here.
