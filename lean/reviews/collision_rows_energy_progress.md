# Actual pivot collision rows and energy

`CollisionRows.lean` and `CollisionEnergy.lean` implement the collision estimate (5.18) on the actual original-angle output sets. The row at a fixed angle contains every pair (competing angle, shared output) with the same original second tube. The direction set is aggregated across every shared output of that angle.

For each competing first tube, the actual row embeds into the product of its actual marked-angle set and the fixed angle's actual outputs whose intermediate label occupies both first tubes. The three proved geometric bounds are:

- Common intermediate labels: C / max(projective distance, delta), including identical first tubes.
- Pivot outputs for each intermediate: 4 boxConstant(n,n/2) (1+2 width) / delta.
- Original marked angles for a fixed pair of tube indices: C / (2 kappa), using the injective original vertex label.

Thus the fixed-first row bound is fixedFirstConstant(n,width) / (kappa delta max(angle,delta)). The proved all-output thin-plane count supplies the linear cap population; the existing actual dyadic inverse-angle sum sums it with logarithmic depth, including the bottom shell.

In ambient dimension n=k+2 the complete result is

    collisionEnergy(Omega) <= rowConstant(k,width) * (log_2(2/delta)+2)
                              * #(original marked angles)
                              / (kappa^(k+1) delta^2).

The row constant is explicit, positive and independent of scale, density, kappa, sample choices, tube count and angle population. The premises are actual admissibility and delta separation, 0<delta<=1, 0<kappa<=1, width>=0, and (6 width/kappa)delta<=1/2. Omega is a literal subset of actual angle-output edges with one common original second-tube label at every output. The independently constructed most-frequent-label selection gives exactly this last property. No direction count, intersection count, row estimate, or collision-energy estimate is assumed.

The final energy comparison encodes an ordered collision as (first angle, second edge). This is injective because the common output reconstructs the first edge. Consequently the sum is over the original angles, not over angle-output edges; no unwanted total-output factor appears.

Both source modules compile without diagnostics. Full-source dependency audits and the frozen whole-package verification provide the definitive checkpoint certification. The complete pivot still needs the selected lift, grouped analytic pruning, energy-position correspondence and exponent assembly.
