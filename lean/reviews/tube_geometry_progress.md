# TubeGeometry checkpoint

6 September 2026. Development module: `audit_work/formalization/TubeGeometry.lean`.

## Completed and compiled

Twenty-four theorem statements now compile under the local Lean 4.33.1/mathlib development project. The final compile completed with exit status zero and no warnings. Representative axiom checks (`legal_pivot_mem_openSegment`, `normalized_perturbed_lift_range`, `rounded_triple_parameter_bound`, `projected_tube_parameter_bound`, `legal_pivot_stem_separation`) contain only `propext`, `Classical.choice`, and `Quot.sound`. No custom axiom, `sorry`, `admit`, or unsafe declaration is used. The file imports the previously compiled `Reduction` vector identities and metric estimate.

This is substantive geometric progress beyond scalar exponent checks. It is still not a proof of the full Kakeya theorem.

## Exact scope

### Legal samples and pivot geometry: PDF (5.11), (5.15), (5.21)

- A legal sample `0<a<b` puts the exact pivot in the actual `openSegment` between the two endpoint vectors, for either sign of the second-axis coordinate `c`. The closed-segment consequence is also proved.
- Keeping the upper length bound as `B`, the two convex coefficients are at least `k/B`, and the absolute coefficients `|u|` and `|c-u|` are at least `k^2/B` under the legal sample hypotheses.
- The exact original lift parameter is proved equal to `b/(b-a)` and belongs to `[1+k/B,B/k]`; its positivity is proved, not assumed.
- A denominator survives a perturbation by at most half its lower bound. Division continuity is quantitatively proved with explicit denominator bounds, giving `|c/v-c/u| <= 2|c| eta/r^2` when `|u|>=r` and `|v-u|<=eta<=r/2`.
- The perturbed lift range is deduced from these facts. In normalized lengths (`b<=1`, `k<=|c|<=1`, `0<k<=1`), the explicit condition `eta<=k^5/4` suffices to give `1+k/2<=c/v<=2/k`. Thus the manuscript's stronger scale requirement has ample room for this particular metric step.

The existence and counting of legal sample tuples from two-ends shadings have not been formalized by this module.

### Exact lift residual and endpoint rounding: PDF (5.31)

- `pivot_residual_bound` derives a norm bound for the actual vector defect from the previously proved exact pivot identity. Given denominator lower bound `r`, norm bounds on axis vectors, and scalar perturbation size `eta`, the residual is at most `eta*(B/r+T)`. A bound on the residual is not substituted as an input to this theorem.
- `rounded_pivot_residual_bound` propagates coordinate-rounding errors of size `delta` at both endpoints and the pivot, adding only `(2T+2)delta` to the residual bound.
- `separation_after_rounding` proves that an exact separation `r` falls by at most `2delta` when both points are rounded.
- `rounded_triple_parameter_bound` allows *different exact endpoint/pivot representatives* for the two incidences, sharing only their rounded labels. With exact first-incidence separation `r` and `delta<=r/4`, it gives

  `|t-s| <= 4*(R+(2T+2)delta)/r`.

  This distinction is essential: distinct angles producing the same rounded triple need not have identical exact representative points. The theorem does not impose that false coincidence assumption.

The remaining task is to turn this interval bound and horizontal coordinate localization into a finite lattice-cell count. No such count is silently assumed in `TubeGeometry`.

### Projection along noncollapsed directions: PDF Lemma 2.1

For a continuous linear map `P`, the exact projected distance of two axis points is `|t-s|*norm(Pv)`. If `norm(Pv)>=c>0`, projected distance at most `r` implies longitudinal separation at most `r/c`.

The full tube-error version permits offsets `e1,e2` with norms at most `delta`, and `norm(P)<=K`. It proves

`|t-s| <= (r+2K delta)/c`.

This is the deterministic geometric interface ensuring only boundedly many original longitudinal cells can collapse into a projected target cell. It does not yet count those cells, select a random map, estimate its small-ball probability, or apply Wolff's theorem.

### Actual orthogonal transversality: PDF (5.15)

The module defines the genuine perpendicular component `v-inner(u,v)u` for a unit stem vector. It proves perpendicularity, norm contraction from Pythagoras, and the squared-norm identity `norm(v_perp)^2=norm(v)^2-inner(u,v)^2`.

It then proves that the pivot's distance from *every* point of the first axis is at least `|u_coefficient|*norm(v_perp)`. Combining this with the legal coefficient bounds yields the explicit `k^3/B` stem-separation lower bound. A distance-to-axis conclusion is not used as an input. The transversality hypothesis is the ordinary quantitative lower bound on the perpendicular component.

## Constants and next interfaces

No displayed scale or density exponent changes in these metric lemmas. The stem separation is `k^3/B`, the perturbed lift range is `1+k/2` to `2/k` in normalized lengths, and the endpoint-triple parameter interval has the expected inverse-power dependence after substituting `r ~ k^3` and `R ~ k^(-2)delta`. Thus the metric stage is compatible with the PDF's `O(k^(-5)delta)` interval and its weakened `O(k^(-6))` energy-position count. The lattice count itself still needs proof.

Next substantive dependencies are integer-grid ball/segment counts, the horizontal/vertical lift-cell support bound, construction of the finite selected fibers and attached pairs, the geometric collision shell count, and the probability/analytic input interfaces. The next module can use the rounded-triple theorem to derive support cardinality rather than postulating it.

Compile command used from the development project:

```
/Users/ssoh/.elan/bin/lake env lean TubeGeometry.lean
```
