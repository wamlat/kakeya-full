# Joint full/marked unit-segment normalization

Three new constructive modules are frozen and clean-built. They close the concrete joint full/marked segment and density-recovery issue in the anisotropic normalization. They add 29 theorems and 10 definitions. Exact full-source audits inspect all 39 named declarations, using only `propext`, `Classical.choice`, and `Quot.sound`.

## Concrete choice and restricted-union support

`AnisotropicJointShading` chooses `bestSegment` using the **marked** shading `G_i`. It defines the full output by intersecting the exact image of `Full_i` with that same chosen carrier; the marked output is the exact image of `G_i` intersected with the same carrier. Nestedness, measurability, finite volume and actual unit-carrier containment are proved.

The input `Full_i` can be the actual restricted angular reference shading supplied by `AngularRestrictedMeasurable.Full`. No old unrestricted full shading is substituted. The output full union is contained in the common anisotropic image of this precise input full union; its real volume is at most the input full-union real volume divided by `tau^k`, in ambient dimension `k+1`.

Every original index initially retains exactly one transformed unit segment. The marked-best choice preserves at least `1/N` of each original marked mass after the exact Jacobian factor, where `N=ceil(1+angular)+1`. No lower marked mass on each original tube is assumed. Choosing a segment independently using full mass would not provide this marked-mass guarantee and is not used.

## Actual measured density recovery

`MeasurableMarkedSelection.select` is a general finite measurable-set theorem. It starts from an original full upper mass `2*lambda`, a total retained marked budget `eta*lambda*M`, and actual subset relations. It performs three proved steps:

1. Remove tubes whose retained marked mass is below `eta*lambda/2`; at least half the total marked budget remains.
2. Select a dyadic **full-mass** class, weighted by actual retained **marked** mass.
3. Retain marked points only where the multiplicity of all original reference marks is at most `8*(D+1)/eta` times the selected marked multiplicity. Integration of actual finite measurable multiplicities proves that at least half the selected marked mass survives.

The original reference multiplicity keeps all original indices. Broadness is therefore transferred through the actual proportional comparison; arbitrary tube thinning is never assumed to preserve it. Actual full sets stay unchanged during the density-class and proportional-mark steps. Separate lemmas derive inherited full two ends and unchanged separation, real-cap bound and base bound under the final injective original-index restriction.

## End-to-end anisotropic theorem

`AnisotropicJointRecovery.construct` starts from actual nested measurable `G_i⊆Full_i` in original unit-tube carriers, a common angular cap, an actual total marked budget, full upper mass, original full two ends at all radii above delta, and original pointwise power broadness of the marks. It constructs the shared segment choices and the actual measured class/filter above.

Write `eta'=eta/N` and `lambda'=lambda/tau^k`. The theorem constructs a nonempty finite original-index class `T`, a dyadic mass density `d`, and measurable full/marked outputs `Z_i,H_i`, with:

- `H_i⊆Z_i` in the same actual transformed unit carrier;
- `d≤volume.real(Z_i)<2d`, with `eta'*lambda'/2≤d≤2lambda'`;
- `D+1≤log(4/eta')/log(2)+2`;
- total output marked mass at least `eta'*lambda'*M/[4(D+1)]`;
- marked/full total mass ratio at least `eta'/[8(D+1)]`;
- pointwise marked broadness, at every physical point, with coefficient `K*[8(1+2angular)^2]^beta * 8(D+1)/eta'`;
- full two ends with coefficient `B*4/eta'` for all radii at least `delta/tau`;
- exact restricted-union containment and volume comparison with factor `tau^(-k)`.

There is no per-tube marked lower-density hypothesis. Some final tubes may have empty final marks; the full comparable density and total marked mass are the relevant conclusions.

`density_parameter` proves the fixed sampling normalization. If the source mass parameter is `lambda_phys*delta^k` with `lambda_phys≤1`, set

`lambda_new=d/[2*(delta/tau)^k]`.

Then `eta'*lambda_phys/4≤lambda_new≤lambda_phys≤1`. The output full masses lie in `[2*lambda_new*(delta/tau)^k,4*lambda_new*(delta/tau)^k)`, so the later sampling density constants are the fixed `c₀=2,C₀=4`, independent of eta, D, the individual tube masses, and the chosen class.

## Scope and remaining assembly

These are geometric/measurable normalization theorems, not a new global Kakeya estimate. The end-to-end theorem explicitly assumes physical full two ends, pointwise marked broadness, local angular containment, positive total marked budget and positive population. It does not assume any sampling outcome, desired union lower bound, per-tube marked density, arbitrary broadness-preserving thinning, or joint-segment mass oracle.

To form the final configuration-facing sampling input, actual bounded bases after the common spatial-box normalization, transformed separation/cap bounds and the appropriate logarithmic parameter budgets must still be supplied by the existing geometric interfaces. In particular, the theorem does not silently treat a merely bounded angular group as one spatial box. The generic class restriction preserves those direction/base properties once they have been proved for the actual transformed family.

The sibling agent independently reviewed the three mathematical statements and proofs, including the all-reference broadness denominator and the fixed density normalization, and reported no substantive defect. Its separate report records the exact boundaries.

## Source identity

| Module | Theorems | Definitions | SHA-256 |
|---|---:|---:|---|
| `AnisotropicJointShading.lean` | 13 | 3 | `70186dfa8ecbae8554574661f1d2d603138ac524d6237716dfff97133dd1b544` |
| `MeasurableMarkedSelection.lean` | 14 | 5 | `fbd039d2b1bef6ba31f682b4d6e12c29418541ba65641184853f2035443b9dc7` |
| `AnisotropicJointRecovery.lean` | 2 | 2 | `e72abfe08c726cb8155d98c1def26ffe903c88547bfb3531aa8240f8e21f707f` |
