# Actual single angular-box hairbrush assembly

Four new modules are complete, compiled and available as `.olean` files in the development project. All 22 theorems were audited individually; every axiom list is a subset of `propext`, `Classical.choice`, and `Quot.sound`. The source contains no `sorry`, `admit`, or custom axiom.

| Module | Theorems | Definitions |
|---|---:|---:|
| AngularBoxSelection | 7 | 1 |
| AngularBoxRecovery | 4 | 6 |
| AngularBoxHairbrush | 6 | 1 |
| AngularBoxAlgebra | 5 | 1 |
| Total | 22 | 9 |

The principal theorem is `KakeyaFormal.AngularBoxAlgebra.single_box_quadratic_density`. In ambient dimension `n=k+2`, it proves

`C λ² M δ^(n−1) (δ/τ)^((m−1)/2) / hairbrushLog(k,δ/τ)^(5/2) ≤ volume(⋃ Ref_i)`.

This is an actual bound on the original measurable reference union. The coefficient `C` is the explicit `densityConstant`; it is positive and independent of λ, δ, τ, and M. The theorem `physical_angular_power` separately verifies the exact factor

`δ^(n−1)(δ/τ)^((m−1)/2) = δ^(n−1+(m−1)/2) τ^(-(m−1)/2)`.

## Inputs and scope

The data are actual measurable `Ref_i ⊆ Full_i`, with `Full_i` contained in its original unit tube of radius δ. Original directions are δ-separated, satisfy the actual real-m cap bound with coefficient A, and all lie in the angular cap of radius `aτ` about a unit direction. The full measures are at most `2λδ^(n−1)`, and the total reference mass is at least `ηλδ^(n−1)M`. Broadness is a literal pointwise finite cap population test for the original `Ref` at angular scale τ. The physical-ball two-ends tests concern original `Full`, only for radii between δ and 1.

Parameter assumptions are `M>0`, `0<δ≤τ≤1`, `a≥0`, `0<η≤1`, `0<λ≤1`, `B,K,A≥1`, `α,β>0`, and `m≥1`. The statements impose no integrality on m. There is no extra spatial-box containment hypothesis: the actual anisotropic carrier cover works for arbitrary bases, so the translation label q can be chosen arbitrarily, for example zero.

The proof does not take any of the following as hypotheses: a selected segment, a coloring, a retained color mass, good indices, marked mass, separation of the recovered family, a hairbrush energy bound, or an enlarged grid-shading volume comparison. These are all constructed or derived.

## Construction and exact constants

Set `H = 8(1+2a)²`, `σ = 1/[4(1+2a)²]`, `S = segmentCount(a)`, `P = paletteSize(n−1,σ)`, and `e = η/(SP)`. These counts depend on dimension and a, not on either scale or the original population.

1. Apply the same exact anisotropic affine map to every `Full_i` and `Ref_i`; actual volume is multiplied by `τ^(-(n−1))`.
2. Choose the actual maximum-mass unit segment of each transformed reference shading, using the proved finite segment cover.
3. Construct a complete finite coloring of the transformed directions, whose original separation is `σδ/τ`.
4. Select an actual color of at least average total mass. Use its selected segment shading on that color and the empty set elsewhere. The reference family still contains every original index.
5. Apply `MeasurableDensityRecovery`. Positive output density forces good indices to belong to the chosen color, hence the recovered family has exact separation δ/τ. Its shadings have normalized densities between `eλ/2` and `2λ`; marked mass is at least `eλ(δ/τ)^(n−1)M/4`.
6. Transport actual cap bounds and reference broadness and invoke the already proved actual all-scale hairbrush kernel. The chosen union is contained in the common exact image of the original reference union.

The transformed/recovered coefficients are

`A' = packingConstant(n−1) A H^m`,

`B' = 4B/e`,

`K' = 8K H^β/e`.

Writing `r=(2B')^(-1/α)` and `θ=(2K')^(-1/β)`, the coefficient in the principal theorem is exactly

`C = (rθ)^(n−1) e^(5/2) / [16 allScaleConstant(k) sqrt(A')]`.

The quadratic density exponent is not an informal simplification: `density_factor_identity` proves the scalar equality that combines selected lower density, common upper density, and retained marked mass. In particular the factor `e^(5/2)/16` is exact for this proof.

## Verification and remaining work

Each of the four files compiled to an `.olean` with no warnings. `AngularBoxAudit.lean` imports the final module and prints the axioms of all 22 new theorems; it completed with exit status zero and only the standard axioms listed above.

The result completes one broad angular piece, including all normalization and selection choices. It does not by itself prove the full angular decomposition, summation over all pieces, logarithmic loss bookkeeping for decomposition-dependent η/B/K, or the manuscript's complete fractional seed and subsequent globalization. The scalar agent is constructing the actual finite angular groups and their whole-cell measurable realization to supply these one-piece inputs. The separate root integration is responsible for the global summation and final `RealCapEstimate` statement.
