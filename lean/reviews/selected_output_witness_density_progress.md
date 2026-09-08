# Actual selected-output witnesses and retained density

`SelectedOutputWitness.lean` closes the actual sample adapter for the grouped normalized incidence set. The input is the actual selected output P, its simultaneous LineData records D, any common color map and normalized shadings contained in the actual common shifted selected cells.

For every normalized cell, undoing its own output's slab shift produces a cell in that same D(q).cells. Its already selected representative defines AttachedSample, with original endpoint labels and original pivot/intermediate labels. Both endpoint labels are proved to lie in the original full family union. The attached sample's energy position is exactly the originalPosition of that cell's actual pivot/slab group.

The grouped sample map is totalized with one actual default selected-cell witness outside the incidence set. Every theorem uses actual incidence membership or T subset S, so the default is never used by a counted incidence. There is no assumed witness, occupied-endpoint condition or energy-position identity in `retained_energy`. It constructs these data internally and applies the proved actual geometric count bound to every T subset of the literal grouped incidence set.

The output is

    |T|² ≤ |F.unionCells|² (Cp/delta_n) (Cl/kappa_n^5)
            sum_p degree(T, actualGroupedPosition, p)²,

with delta_n=delta/(1+2width), kappa_n=kappa/(1+2width) and error C=2width+(ambient+1)/2. The geometric fifth-power perturbation test remains explicit. All color groups and center-defined original slab positions are preserved; no color-count or slab-count factor is introduced in the witness energy.

`SelectedOutputDensity.lean` defines rho from the actual normalized grouped incidence set, rather than the pre-normalization KQ population:

    rho = delta_n |S| / Q.

The actual selected output type is proved nonempty, hence Q>0. If each normalized shading keeps at least K/3 cells, then

    rho ≥ kappa^6 sigma /
      [60 multiplicityConstant(ambient,2width) (1+2width)^7] > 0,

where sigma=2^level delta uses the original mesh. The factor three is paid explicitly. Containment in the shifted original selected cells bounds each normalized shading by K, because that common shift is injective. Actual pivot-fiber geometry then bounds rho above by a fixed geometric constant, including the nonempty-floor branch of K.

These modules compose actual objects and preserve the distinction between the original and normalized meshes. The next bridge uses the exact grouped analytic pruning output on these same constructed normalized colored families. The original-scale closing algebra must include the fixed homothety factor before the source output-count substitution.

## Verification

Both modules clean-build to .olean and pass fresh full-source environment audits, including generated theorem declarations, with no compiler warnings. Only propext, Classical.choice and Quot.sound occur; there are no custom axioms or admissions. These are later modules than the frozen checkpoint11 snapshot and await a subsequent full-package checkpoint.

- SelectedOutputWitness: 6 source theorems; 16 local theorem declarations audited; SHA-256 `1ff2bdbadd8bfb912483b88f9b85c3ae1327a4ef6385ce23693baf2b9ce54e0e`.

- SelectedOutputDensity: 6 source theorems; 23 local theorem declarations audited; SHA-256 `6c07da2811efeb9fd37af38c27d254823cf699d74d40cdd5bfe13c8d5b01f3ee`.
