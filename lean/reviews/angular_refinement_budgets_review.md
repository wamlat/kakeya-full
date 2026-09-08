# Independent review: actual angular and spatial logarithmic budgets

Reviewed 2026-09-06. No mathematical defect was found in the final reviewed versions of `AngularRefinementBudgets.lean` and `AngularSpatialBudgets.lean`, including `total_population`. Both were read in full and independently recompiled with matching dependencies using `lake env lean <module>.lean`; both returned exit 0 with no diagnostics. No shared or frozen source was changed.

| Source | Reviewed SHA-256 |
|---|---|
| `AngularRefinementBudgets.lean` | `a7dc3fa2a4f4fbfc11e54b9fb8ba3b3457f6f1222a419711bcf924798d20276b` |
| `AngularSpatialBudgets.lean` | `6bd38927695f00aa76722a52d83f5c2652e23bf6351f84d0710efd255d94e50b` |

The review checked the underlying literal constants and data fields in `AngularSeedPieces`, `AngularRestrictedRefinement`, `AngularSpatialSampling`, and the proved budget lemmas of `AnisotropicSamplingBudgets`.

## Reference refinement

Write `L = log(2/δ)`, `h = 3/log 2`, `etaC = etaBase k/h`, and `Cd = depthCoefficient etaC 1`. Positivity of these constants is explicitly proved. They depend only on the fixed dimension at this stage.

The source correctly proves `seedLog δ ≤ h L`, retaining the additive `+2` in the base-two logarithm. Inversion therefore gives the genuine natural-log lower bound `P.eta ≥ etaC L⁻¹`; its direction is correct. Applying the already proved depth estimate to the actual refinement's `log(4/P.eta)` bound gives `V.depth+1 ≤ Cd L`.

The resulting exact budgets are:

| Actual quantity | Proved bound |
|---|---|
| `P.eta` | `≥ etaC L⁻¹` |
| `V.depth+1` | `≤ Cd L` |
| `1/[4(V.depth+1)]` | `≥ [1/(4Cd)] L⁻¹` |
| `V.N` | `≥ [etaC/(32Cd)] L⁻² * activeGroupCount` |
| `V.density/W^(k+1)` | `≥ [etaC/(2W^(k+1))] L⁻¹ * lam` |

The population coefficient matches the actual marked-mass proof: `P.eta*activeGroupCount/[32(V.depth+1)] ≤ V.N`. The physical-density denominator is the actual ambient volume power `W^(k+1)`. The budget theorem only requires `W > 0`; separate physical-density upper bounds use the stronger normalization hypotheses when needed.

The depth and population estimates explicitly assume `L ≥ 1`. They do not silently infer this from `δ ≤ 1`, which alone only gives `L ≥ log 2`. The eta and density budgets themselves do not introduce that stronger logarithm assumption.

## Spatial conditioning and per-group population

The effective fraction is the literal `retention k 3 (markedRatio V/4)`. Since `markedRatio V = 1/[4(V.depth+1)]`, its fixed coefficient is `retention k 3 (1/(16Cd))`, and its lower logarithmic exponent is one. Segment and separation-color costs remain inside this positive fixed coefficient.

The spatial two-ends constant is the actual original factor `4B/P.eta`, multiplied by the cell-enlargement factor `(1+(k+1)/2)^alpha` and the width-normalization factor `widthFactor^(alpha)`. Substitution therefore gives one power of `L`. The fixed coefficient keeps all these factors and depends on the original fixed `B`, width, dimension, and exponent.

The marked broadness coefficient is exactly

`64 * originalBroadCoefficient * spatialConstant * (V.depth+1)/P.eta`.

Its upper logarithmic exponent is two and its fixed coefficient is `64*originalBroadCoefficient*spatialConstant*Cd/etaC`. All bases of real powers in the positivity proof are strictly positive, including for arbitrary fixed real `alpha` and `beta`; no implicit nonnegative-exponent assumption is needed for that positivity claim. Applications establishing concentration bounds retain their separate positive-exponent hypotheses.

The actual spatial population theorem gives at least `markedRatio V * V.N/4` tubes summed over the full defining set of good boxes. Combining the two actual lower budgets yields

`[etaC/(512 Cd²)] L⁻³ * activeGroupCount`.

This is exactly `boxPopulationCoefficient`. The sum runs over all `boxes V width`; no further favorable-box selection or additional unaccounted loss is used.

## Total population over retained angular groups

The final `total_population` additionally uses the actual pruning conclusion

`(3*retentionRate/8)*M ≤ sum activeGroupCount`.

Because `P.eta = retentionRate/4`, the coefficient is `(3/2)*P.eta`, giving the fixed natural-log lower bound `(3*etaC/2) L⁻¹ M`. Multiplication by the per-group spatial coefficient yields exactly

`[boxPopulationCoefficient * (3*etaC/2)] L⁻⁴ M`.

The dependent sum is over the actual subtype of `P.keptGroups lam`; the conversion from the finite filtered sum preserves that set exactly. Each summand uses the supplied refinement for that same group and the corresponding `SpatialData` for the same good-box set. No cardinality equality between different indexings is asserted without the proved finite-sum conversion.

The statements adapt actual `Pieces`, `Refinement`, and `SpatialData` returned by separate construction theorems. In particular, `SpatialData.population` is a previously proved geometric output, not something newly derived by a scalar budget lemma. The actual constructors are available in the inspected dependency modules and must be used when assembling the final theorem; this boundary is explicit.

## Uniformity and remaining assembly

All displayed coefficients are explicit functions of fixed dimension and fixed normalization/exponent constants. They contain no actual mesh, angular scale, group, selection depth, density, population, or cap coefficient. Their positivity and every natural-log exponent are proved. The `L ≥ 1` condition must be supplied by the uniform small-scale branch, with the complementary bounded-scale branch handled separately.

The reviewed modules provide the conditioning, density, and total population needed for summation. They do not themselves prove a per-box analytic estimate, compare the original and normalized logarithms without a scale premise, invoke the actual box outputs, or sum old-cell union inequalities using the angular overlap bound. Those are separate assembly steps.
