# Actual anisotropic sampling input

`AnisotropicSamplingInput.lean` is frozen and clean-built. Its 3 theorems and 4 definitions all pass an exact full-source audit using only `propext`, `Classical.choice`, and `Quot.sound`. No custom axiom, placeholder, supplied sampling outcome, or expectation oracle is used.

## Constructed objects and hypotheses

`construct` starts with actual nested measurable full/marked sets in the original width-delta unit tubes; original delta-separated directions and a real-m cap bound; a common angular cap; and original bases in a literal common `parallelBox u tau q R W`. It requires `0<delta≤tau≤1`, nonnegative width/angular parameter and alpha, positive beta/K, `B≥1`, `0<eta≤1`, `0<lambda≤1`, positive population, original full mass at most `2*lambda*delta^k`, total original marked mass at least `eta*lambda*delta^k*M`, original full two ends at every radius at least delta, and original pointwise marked broadness at angular scale tau.

The source ambient dimension is `k+1`. The given full set can be the precise restricted angular/spatial reference shading. No unrestricted old full shading is substituted.

The proof constructs, in order:

1. The actual unit segment selected using each original marked shading, with full and marks in the same carrier.
2. A fixed finite direction coloring and a color selected by marked mass, retaining at least the average `1/P` share. The certified property is this mass bound; no separate argmax identity is needed or asserted.
3. An actual dyadic full-mass class selected by retained marked mass.
4. Actual proportional marks, using the multiplicity of **all original exact image-G reference rows** as denominator.
5. An injectively reindexed actual family and measurable full/marked sets `Fnew,Z,H`.

The color is selected before measured recovery. There is no assertion that coloring an already recovered broad family preserves broadness.

## Exact sampling Input

Let

`N=segmentCount(angular)`, `P=paletteSize(k,separationFactor(angular))`,
`e=eta/(N*P)`, and `delta'=delta/tau`.

The theorem constructs a depth D, class index ell, nonempty original-index class T, and density `lambda_new` satisfying

`e*lambda/4 ≤ lambda_new ≤ lambda ≤ 1`,
`D+1 ≤ log(4/e)/log(2)+2`.

It proves the actual record

`SamplingNormalizedMeans.Input Fnew Z H delta' width Rnew lambda_new 2 4 xiNew BNew alpha KNew beta`,

where

- `Rnew=1+|R|+|W|+N`;
- `xiNew=e/[4(D+1)]`, with `0<xiNew≤1`;
- `BNew=4B/e≥1`;
- `KNew=K*[8(1+2angular)^2]^beta * 8(D+1)/e>0`.

In particular the full masses lie between `2*lambda_new*delta'^k` and `4*lambda_new*delta'^k`. The constants 2 and 4 are fixed independently of the original marked fraction, depth, class, density, scale and individual tube mass.

The marked Input budget follows from actual retained marked/full fraction `e/[8(D+1)]` multiplied by the full lower density 2. The original marked reference population is kept through this calculation and through the broadness transfer.

## Actual geometry and union comparison

The output family is exactly delta'-separated, because positive measured full density forces membership in the selected color. It has actual cap coefficient

`packingConstant(k)*[8(1+2angular)^2]^m*A`.

For every output index i, `Z_i` lies in the anisotropic image of the same original `Full_(index T i)`. The theorem also preserves the original-population marked budget

`sum_i volume.real(H_i) ≥ e*(lambda*delta^k/tau^k)*M/[4(D+1)]`

and proves

`volume.real(union Z) ≤ volume.real(union original Full)/tau^k`.

Thus the input feeds `SamplingMeasurableAssembly` without supplying full/marked probability arrays, expectations, finite test counts, or a density/geometry oracle.

## Remaining boundary

No logarithmic budget theorem or small-scale threshold is proved here. The future composition must derive the budgets for `xiNew,BNew,KNew` and the required scale/density branch conditions before applying the actual sampling theorem and pivot bound. The common spatial-box premise remains literal and is supplied by the separately constructed actual spatial marked partition; an entire angular group is not assumed to occupy one box.

The source full two-ends assumption is stated for all radii above delta, matching the existing actual restricted-measurable/group interface. The output Input only needs tests up to radius 1. The source pointwise angular broadness yields the a.e. broadness field of Input.

The sibling agent independently reviewed the full statement/proof, checked the marked fraction factor, the all-reference denominator, actual colored family identity, density scaling, and restricted-union support, and found no substantive defect. Its separate review report records those checks.

## Validation

- Clean original compile and `.olean` build, without warnings.
- Seven exact-source axiom reports, all standard foundations only.
- Source-audit prefix checked equal to the complete frozen source.

Source SHA-256: `92ad6a8897b33f82eb926cedb716f6f40686377bbabbc22d5542bc026b6d2fd4`.
