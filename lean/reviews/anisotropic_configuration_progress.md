# Complete configuration-facing anisotropic box normalization

AnisotropicConfiguration.lean constructs an actual MeasurableConfiguration from one actual angular/spatial box. It imports the geometric and measurable results rather than assuming transformed admissibility, density, cap conditions or union comparison.

In ambient dimension k+1, let N=ceil(1+angular)+1. The fixed tube-volume constants are c_k=unitBallVolume(k+1)/2^(k+2) and C_k=3*2^(k+1)*unitBallVolume(k+1). The retained density factor

f(k,angular)=c_k/[(C_k+c_k)*N]

is proved positive and≤1. Each best-segment selected image shading retains relative density at least old_density*f in its actual new unit tube, by the two-sided actual carrier volume bounds. This is a relative-volume statement, not merely a cardinality estimate.

An original tube base in the concrete parallelBox(u,tau,q,R,W) becomes a selected unit-tube base of norm≤1+|R|+|W|+N. The target fixed normalization has this radius and separation coefficient old_separation/[4(1+2|angular|)^2]. All these constants are fixed before the varying scales, density, tube number and configuration.

The construction normalize produces new scale delta/tau, new density old_density*f, new cap coefficient packingConstant(k)*old_A*[8(1+2angular)^2]^m, and the exact selected measurable shadings. Every MeasurableConfiguration field is proved, including scale≤1, density≤1, A≥1, measurability, actual unit carrier containment, individual relative mass, bounded bases, direction separation and cap bounds. Assumptions are m≥0, angular≥0,delta≤tau≤1, unit stem, all participating directions in the local angular cap, and each base in the actual parallelBox. It still requires the input group to be represented as its actual participating tube family, not an old full index set padded with empty shadings.

The normalized union has volume≤old union volume/tau^k. The theorem estimate_on_box then proves the exact conditional estimate: if MeasurableEstimate(k+1,m,d,p) is available, for each fixed geometry, angular width, box widths and epsilon>0 there is c>0 such that every such actual box satisfies

c*A⁻1*delta^(k+1+m-d+epsilon)*density^p*M*tau^(d-m-1-epsilon) ≤ volume(original union).

The constant is selected before the configuration and tau. The statement remains conditional on the existing measurable estimate; it is not a new proof of that estimate or of the Kakeya endpoint.

Verification: Lean4.33.1, Mathlib commit0df444a360eaa60ab8c11dca51a86af692955474. Clean .olean build from audit_work/formalization. Full-source audit anisotropic_configuration_axioms.lean/log checks all12 theorem declarations plus the proof-bearing normalize and targetGeometry constructions:14/14 dependency lists use only propext, Classical.choice, Quot.sound. No sorry/custom axioms.
