# Independent finite-agent review: actual projected grid family

Read-only statement/proof review of both frozen sources and their concrete geometry dependencies. Clean .oleans are present; **no substantive defect found**. Source hashes:

| Source | SHA-256 |
|---|---|
| `ProjectedGrid.lean` | `7ce2f4373b7ff11280775ead5eed783ef76599fa3d3c69861696babb11807faa` |
| `ProjectedGridFamily.lean` | `92744d3882fc76cb440fb5ffcecab5757adb2857fa371d8a986bfbba3d6d532f` |

This review covers mathematical linkage and scope, not a duplicate source dependency audit.

## One common original-label map

`labelMap P delta z` rounds the actual point `P(cellCenter delta z)` in the target grid at the **same mesh delta**, independently of the tube or shading row. Exact target half-open cell coverage gives the target center-distance bound d*delta/2, hence two original labels with the same target label have projected centers at distance at most d*delta. There is no assumed label injectivity, shifted per-tube grid, or different map for different rows.

## Proved original-cell fiber geometry

For labels on one original unit tube with `||Pv|| >= c > 0` and `||P|| <= K`, actual projection errors have norm at most K*width*delta. The previously proved longitudinal parameter inequality gives `|t-s| <= (d+2K*width)*delta/c`. Adding the two original tube-width errors gives the exact radius

`Rfiber = 2*width + (d+2K*width)/c`.

Choosing one actual label from a nonempty fiber then puts all its original centers in a ball of radius Rfiber*delta. The original n-dimensional integer-grid counting lemma, with no alignment assumption, bounds the fiber by `(2*ceil(Rfiber)+3)^n`. The empty-fiber case is explicit. Thus the exponent is the **original dimension n**, while d enters only the target rounding error; these conventions are correct. Summing the literal fibers gives the actual row image-cardinality lower bound. No fiber bound or projected density conclusion is assumed.

Width need not be separately assumed nonnegative in these generic statements: any nonempty incidence with delta>0 already forces width>=0, and the empty row/fiber conclusions remain valid. The universal finite-grid bound is valid even when its supplied radius is negative (then the incidence is empty); no unjustified positivity is used to divide by that radius. Division occurs only by c and by the explicitly positive natural fiber constant.

## Actual finite projected axes and support

The target UnitTube stores base P(base) and unit direction Pv/||Pv||. Its physical axis length is retained separately and exactly as `lengths=||Pv||` in [c,K]. `axis_image` identifies `t*||Pv||` on that normalized axis with the image of the original t. Therefore the carrier conclusion is the actual finite **lengthCarrier**, with width `(K*width+d/2)*delta`; it does not falsely claim a unit-length carrier contains the image when K>1.

Every target shading is exactly the image of the same-index original shading under the common map. `union_image` proves the full union is exactly the image of the original union, and `union_card_le` follows immediately. Row upper bounds are literal image-cardinality bounds; lower bounds use the proved same-tube fiber constant. Fixed original lower/upper density multiples are preserved up to that fixed constant. In particular `density_bounds` states the interval `[lambda/(Cfiber*delta), 2lambda/delta]`; it does **not** assert the stricter factor-two `TubeFamily.Comparable` predicate without further trimming. This distinction is explicit in the actual theorem statement.

The final `construct` has only original-map geometry, noncollapse and original admissibility inputs. Its projected axes, lengths, carrier incidence, support identities and row counts are all derived. It keeps the original index type and permits empty shading rows. Projected separation/cap bounds, choosing a Gaussian realization/subfamily, and later unit-length normalization are not claimed by this module; they must be supplied by the independent graph selection and existing normalization adapters. There is no circular output-geometry premise.
