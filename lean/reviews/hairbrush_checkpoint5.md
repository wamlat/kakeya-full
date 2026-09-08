# Hairbrush verification checkpoint 5

## Completed, kernel-checked mathematical content

Ambient dimension is `d = k + 2`. Every tube is an actual Euclidean unit segment with its closed δ-neighborhood; projective angle is the concrete minimum of the two chord distances between unit direction representatives. Every shading and union is an actual measurable set with Lebesgue measure. The real direction-cap hypothesis is the defined predicate `TubeFamily.CapBound δ m A`, applied to the original tube family.

Stable modules added after the planar geometry checkpoint:

| Module | Theorems | Definitions | Coverage |
|---|---:|---:|---|
| HairbrushUnion | 8 | 2 | Actual finite plane-bin construction, pointwise overlap, integration, and sum of per-bin union bounds |
| HairbrushRemoval | 9 | 2 | Crossing-point choice interface; actual ball removal, half-mass retention, axis escape, automatic bounded location |
| HairbrushStem | 5 | 2 | Integrate actual stem incidence; prove actual bristle count; derive (4.15) |
| HairbrushSelection | 9 | 2 | Actual measurable dyadic multiplicity shells, mass pigeonhole, weighted stem selection |
| HairbrushBroad | 5 | 3 | Complete fine-scale broad hairbrush (4.8), squared form, with stem/bristles/net constructed |
| HairbrushFractional | 7 | 1 | Actual fractional-cap total mass bound and (4.16), squared and unsquared forms |
| HairbrushScales | 9 | 5 | Concrete logarithmic multiplicity depth and density-independent concentration radius |
| HairbrushCoarse | 4 | 1 | Actual coarse union bound and fractional factor bound |

There are no `sorry` terms or custom axioms. Main theorem audits report only `propext`, `Classical.choice`, and `Quot.sound`. All listed source files compile cleanly in the pinned Lean/mathlib environment. Earlier EuclideanSplit, HairbrushPlanes, ThickCircle, PlanarEnergy, TubeIntersection and MeasurableEnergy supply actual geometry and measure theory, not assumed packing or energy estimates.

## Main fine-scale theorem and exact inputs

`HairbrushFractional.real_cap_hairbrush_linear` proves

`W_G λ^(3/2) δ^((m−1)/2) (rθ)^((d−1)/2) / [sqrt(C_d A Λ) L^(5/2)] ≤ volume(U)`.

This is the manuscript's (4.16), physical PDF page 13. Its inputs are:

- A nonempty actual finite original tube family, with δ-separated unoriented directions and actual real-m cap bound A.
- Actual measurable shadings `Y_i` inside their tube carriers, with mass between `λ δ^(d−1)` and `Λ δ^(d−1)`.
- Actual measurable marked set G whose marked incidence mass `W_G = Σ_i volume(Y_i ∩ G)` is at least half the total shading mass.
- At every marked point in every incident tube, the actual number of incident directions within projective angle `< θ` of that tube is at most half the actual multiplicity. This is the needed consequence of angular broadness; broadness is not silently assumed to produce a stem.
- The original measured two-ends tests `volume(Y_i ∩ closedBall(p,t)) ≤ B t^α volume(Y_i)` for every physical center p and every δ≤t≤1, with `B r^α≤1/2`.
- `0<δ`, `0<r,θ≤1`, and the fine-scale comparison `88δ≤rθ`.
- A finite depth J with actual tube count≤2^J, `J+1≤L`, and `log₂(2/δ)+2≤L`. `HairbrushScales` constructs J and L from actual direction packing, using a dimension-only multiple of `log₂(2/δ)+2`; these are no longer independent missing estimates.

The theorem allows every real m at this stage. The all-scale combination uses m≥1 to bound the harmless fractional scale factor at coarse scales. Later angular normalization needs m>1, as in the manuscript.

## Derivation details relevant to the audit

The proof genuinely constructs a multiplicity shell carrying at least `W_G/(J+1)` marked mass, and uses weighted averaging to choose a stem with a large portion in that shell. It constructs transverse bristles by filtering actual original indices for angle≥θ and a nonempty shading intersection with the selected stem portion. An exact finite incidence partition subtracts the actual near-cap count and supplies transverse multiplicity.

For each bristle, the proof chooses an actual common physical point in the shading intersection. Removing the actual closed ball of radius r preserves at least half its mass. The elementary geometric escape estimate is `distance-from-stem-axis ≥ rθ/4` under `20δ≤rθ`. All bristles meeting the unit stem automatically lie within radius5 of its base. Plane nets, plane-bin overlaps, thick-great-circle packing, logarithmic planar row energy, L2, and integration are all derived.

A useful simplification over manuscript page 12 is verified: use the full original bristle shadings after selecting the stem. They remain subsets of the same global union and retain their original two-ends estimates. The manuscript's additional retained-tube and X′ pruning is therefore unnecessary for this broad hairbrush estimate. We preserve the manuscript's weaker logarithmic powers, so this simplification does not enlarge its stated conclusion.

The coarse theorem, valid when `rθ≤88δ`, proves

`(rθ)^(d−1) W_G / C_d ≤ volume(U)`

from actual separated direction packing and integrated multiplicity, with no broadness or two-ends premise. It is the promised elementary coarse-scale mechanism on physical PDF page13.

## Work still required for the manuscript's full fractional seed

This checkpoint is an actual broad hairbrush theorem, not yet a proof of the complete seed predicate (4.4), nor of the manuscript's main dimension conclusion. The remaining assembly must construct the marked broad pieces from the original shadings, transport them through actual anisotropic angular normalization, keep track of their common physical determinant and density interval, sum piece unions with the proved overlap, and absorb the density-independent radius and logarithmic losses. Root and the scalar agent are developing the actual grid-cell/measurable and angular-spatial bridges. Those results must be invoked explicitly; an assumed normalization or seed inequality must not replace them.

`HairbrushAllScales.lean` is now a clean, kernel-checked integration of the fine and coarse kernels (2 theorems, 1 definition). Its common radius power is weakened from `(d−1)/2` to `d−1`, which changes only eventual logarithmic loss when r and θ are inverse logarithmic powers. It retains the exact physical `δ^((m−1)/2)` and density `λ^(3/2) Λ^(-1/2)` factors. It constructs the required logarithm, handles both scale cases, and requires the half-cap condition only when its radius is above δ.

`HairbrushKernel.lean` also cleanly compiles (2 theorems, 1 definition). It defines literal measurable pointwise angular broadness, derives the actual half-cap condition from it, and constructs both radii `(2B)^(-1/α)` and `(2K)^(-1/β)` inside `chosen_radius_hairbrush`. Thus the downstream bridge only needs the original pointwise broadness, two-ends, marked mass and density interval, alongside the actual cap/separation hypotheses.


## Completed logarithmic kernel

`HairbrushLogLoss.lean` adds 6 theorems and 2 definitions. Its actual geometric main theorem `logarithmic_hairbrush_kernel` applies all prior geometry internally. When `B≤B₀ L^b`, `K≤K₀ L^q`, and the concrete local logarithm is bounded by the original reference L up to the explicit dimensional coefficient, it proves

`c(d,B₀,K₀,α,β) L^(-P) W_G λ^(3/2) δ^((m−1)/2) / sqrt(AΛ) ≤ volume(U)`

with `P = (d−1)(b/α + q/β) + 5/2`. The positive prefactor is explicitly constructed from the fixed radii `(2B₀)^(-1/α)`, `(2K₀)^(-1/β)` and dimensional constants. It is fixed before δ, λ, Λ and A. P≥0 is proved when b,q≥0 and α,β>0. This P is larger than the manuscript's fine-scale formula (4.17), because a common radius power was used to include coarse scales. This changes no claimed scale, density, or fractional-m exponent.

The module also proves that increasing physical width decreases the concrete logarithm; this supplies the original-scale log budget for angularly rescaled pieces. No logarithmic concentration or broadness radius is chosen using density. The actual original all-center pointwise cap tests are the input to `PointwiseBroad`; these match the already-formalized finite grid angular broadness API.

The remaining seed assembly is therefore concrete geometric transport and summation of actual broad marked pieces, not the broad hairbrush proof or its logarithmic constant quantifiers.
