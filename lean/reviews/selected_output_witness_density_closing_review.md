# Independent review: selected-output witnesses, density and closing energy

Verdict: no substantive mathematical defect found in the reviewed statements or their composition interfaces. The actual original endpoint labels, dependent output fibers, common slab translations and incidence multiplicities match. This is a conditional closing-energy interface with concrete geometric witnesses; it is not yet a theorem constructing the normalized shadings and grouped-pruning output from the original configuration.

## Review and kernel verification

Read in full: `SelectedOutputWitness.lean`, `SelectedOutputDensity.lean`, `SelectedOutputClosing.lean`, `SelectedOutputSlabs.lean`, `SelectedOutputPairs.lean`, `ActualGroupedIncidence.lean`, `ActualGroupedGeometry.lean` and `GroupedSlabPositions.lean`. Checked the relevant actual count and scalar closing proofs in `ClosingEnergyAlgebra`, `SelectedLiftWitness` and `PivotWitnesses`, and compared with combined PDF sections 5.5–5.7 (extracted lines approximately 1128–1294).

A fresh audit source combines the complete bodies of all three target modules, imports only their external dependencies, and prints the axioms of every local theorem and definition. It compiles successfully without warnings. All 21 declarations have exactly the standard axiom set `propext`, `Classical.choice`, `Quot.sound`; no sorry, admit, unsafe declaration or custom axiom occurs. This checks the actual source bodies, not only imported target oleans.

Audit source: `selected_output_witness_density_closing_audit.lean`.
Audit log: `selected_output_witness_density_closing_audit.log`.

Reviewed source SHA-256 values:

- SelectedOutputWitness: 1ff2bdbadd8bfb912483b88f9b85c3ae1327a4ef6385ce23693baf2b9ce54e0e
- SelectedOutputDensity: 6c07da2811efeb9fd37af38c27d254823cf699d74d40cdd5bfe13c8d5b01f3ee
- SelectedOutputClosing: 685080cb4210d32bd00cd1f375be92ecb9e75b8b2616a4eae540bb024d17a0cc

## Dimensions and scales

In these three modules, local `k` is the original projective direction dimension. The original physical ambient dimension is n = k+1 and the lifted physical ambient dimension is n+1 = k+2. Thus endpoint/pivot labels have type Cell(k+1), lifted labels have type Cell(k+2), and the witness has type AttachedSample(k+1). The error coefficient is C = errorConstant(n,2w) = 2w+(n+1)/2, matching full lifted-grid rounding. Both pivotCoefficient and liftCoefficient use physical endpoint dimension n, not lifted dimension n+1.

Put R = 1+2w, delta_bar = delta/R and kappa_bar = kappa/R. The geometric witnesses consistently use delta_bar and kappa_bar. Their normalized projection width is 2w. Original endpoint labels are unchanged under the SINGLE common homothety: the same integer labels have normalized centers at delta_bar. Their occupied set may therefore remain literally F.unionCells, with unchanged cardinality. This would not justify reusing original physical geometry at delta_bar without the common homothety; the actual pair construction already supplies that homothety.

The exponent convention is compatible with the original output bound: these modules' projective dimension k corresponds to the exponent 5k in the selected-output population estimate. When the earlier PrunedPivotSelection uses original ambient k_old+2, instantiate the present k with k_old+1. No off-by-one factor occurs inside the reviewed code.

## Endpoint witnesses and default branch

For each actual normalized incidence, `unshift_mem` undoes the exact integral label translation chosen for THAT output's slab. `cellSample` uses the representative of this unshifted selected cell in that same output's actual raw pair fiber. `representative_cell` proves its lifted cell is precisely the recovered cell. `representative_original` and `representative_occupied` decode its endpoint labels to a genuinely selected original triple in the chosen angle, and then to the two original full shadings.

The witness's pivot is the same selected output pivot, and its intermediate label is that output's original second component. `cellSample_position` is an exact equality, not an approximate matching or a choice from another output. Its proof uses representative_cell and reference_pivot.

The total map `groupedSample` has a default branch outside the actual incidence set. This does not contaminate any count: retained_energy requires T to be a subset of that set, and both occupied-label and position equalities are proved after eliminating the default branch using actual membership. The default itself is an existing selected-cell witness, with existence derived from positive selected output count and commonK >= 1. No arbitrary inhabitant or inconsistent geometric record is assumed.

Injectivity of the incidence-to-witness map is not required. The inherited energy theorem uses actual finite fiber multiplicities as weights, whose sum is exactly the number of incidences. Multiple incidences with the same triple/position are correctly counted with multiplicity.

## Slabs, grouping and energy positions

The grouped index equivalence retains every original output exactly once, even after adding a color. The uncolored energy position is (original pivot, original slab, shifted cell): only the color is forgotten. Undoing the common grid shift recovers the exact original lifted cell.

The actual half-open center condition j <= delta_bar*z_vertical < j+1 determines the integer slab j uniquely. Thus originalPosition is injective on the legal positions actually used. The grouping-to-original energy equality is exact, including when the retained incidence set meets several slab groups. There is no hidden number-of-slabs factor and no independent translation of different lines within the same base group.

## Actual mass and density

The exact KQ identity applies to the selected cells BEFORE genuine unit-segment normalization. The normalized shading passed to these modules instead satisfies, for each output q,

    K/3 <= |shading(q)| <= K.

The upper bound follows from literal inclusion in the shifted selected cells and injectivity of the common shift. Consequently the actual normalized incidence count I0 obeys KQ/3 <= I0 <= KQ. The code defines rho = delta_bar*I0/Q, rather than replacing I0 by KQ. After half-mass pruning, I >= I0/2 >= KQ/6; no claimed KQ/2 mass is smuggled through the segment-normalization step.

Writing h = 2^level and sigma = h*delta, the common-floor bound gives

    K >= kappa_bar^6*h/(20*multiplicityConstant(n,2w)).

Multiplication by delta_bar/3 gives exactly

    rho >= kappa^6*sigma / [60*multiplicityConstant(n,2w)*R^7].

Thus SelectedOutputDensity.lowerCoefficient has the correct factor 60 and seventh homothety power. The nonempty floor branch is retained. The proved rho upper bound is a fixed geometric constant, not an unjustified rho <= 1 assertion. The cumulative estimate is the correct downstream input for such arbitrary actual density.

## Closing powers and coefficient

The actual endpoint/pivot count costs Cp/delta_bar and the actual lifted-cell count costs Cl/kappa_bar^5. The geometric energy theorem therefore uses kappa_bar^(-5), a stronger bound than the paper's subsequently weakened kappa_bar^(-6). This stronger exponent is proved by the underlying actual cell-count theorem and is not a missing loss. The source version with kappa^6 follows for 0 < kappa <= 1.

For the actual grouped cutoff

    H = 2^(r+1) J delta_bar^(-1)
        / [c A^(-1) delta_bar^(d-d'+eps) rho^(r-1)],

combining energy <= H*I, I >= rho*delta_bar^(-1)*Q/2 and the actual geometric energy lower bound gives

    E^2 >= closingCoefficient * kappa_bar^5 A^(-1)
           rho^r delta_bar^(d-d'+1+eps) Q.

Here J is the common color-count parameter, not the number of pivot/slab groups. No group-count factor is inserted.

With t = d-d'+1+eps, the conversion to original scale is exactly

    kappa_bar^5 delta_bar^t = kappa^5 delta^t / R^(5+t).

The normalization_identity handles arbitrary real t, including negative t, and positivity of the coefficient is proved for every real r,t. The originalCoefficient includes exactly this R^(5+t) denominator. This is consistent with equation (5.33), after weakening kappa^5 to kappa^6 if desired. The condition r >= 2 is needed only later when substituting the sigma lower bound; it is correctly absent from the pure closing-energy implication.

## Explicit remaining interfaces and limitations

1. The target modules accept actual LineData D. Their existence has been proved upstream in SelectedOutputSlabs from selected raw fibers and the stated normalized slab smallness test, but is not invoked within retained_closing.
2. The unit tube/shading construction and all-color normalized cap/separation bounds must supply the actual shading map, shifted-cell inclusion and K/3 lower mass. These are substantive explicit inputs here. No claim that arbitrary maps automatically satisfy them is made.
3. retained_closing assumes hretain and the precise actual uncolored degree-energy upper bound hupper for T. These are exactly the shape returned by ActualGroupedIncidence.actual_discrete_pruning, with r equal to the lifted cumulative exponent, J equal to the actual finite palette cardinality, cap exponent d and target dimension d'. The final adapter must instantiate those values and the same literal shading/position maps. The theorem itself does not invoke the lifted DiscreteEstimate.
4. hscale is the attached-witness test at delta_bar and kappa_bar. It is supplied by the appropriate PivotGeometryScale.Tests field once the original-width/2B/theta choice is instantiated. Original and normalized meshes must remain distinct in that adapter.
5. The right side here is |F.unionCells|^2. If F is a recovered family, its inclusion in the literal original pruned union (and then original comparison E) must be used explicitly when expressing the final inequality in original comparison variables.
6. The final substitutions of the output population, rho lower bound, sigma lower bound and spatial pruning threshold are downstream. The three reviewed modules alone do not prove the full pivot estimate or the final dimension conclusion.

These are accurate, visible scope boundaries; none is a defect in the reviewed conditional statements.
