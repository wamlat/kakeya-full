# Actual crossing-ball removal

`HairbrushRemoval.lean` has 9 theorems and 2 definitions. Actual unit-tube carriers have diameter ≤1+2δ and base distance≤1+δ. A bristle meeting a unit stem is automatically within radius5 of the stem base. Given an actual common point p, any bristle point at distance≥r from p has stem transverse distance≥rθ/4 whenever20δ≤rθ and its projective angle from the stem is≥θ. The proof derives every axis approximation and transverse error.

The measurable set `outsideCrossing Y p r` is exactly `Y \ closedBall(p,r)`. A measured ball concentration≤half the original mass proves half-mass retention. The final theorem `two_ends_crossing_hairbrush` derives ball concentration from actual two-ends tests and B r^α≤1/2, chooses the far distance s=rθ/4, and obtains

`#H λ² δ^(d−1) (rθ)^(d−2)/(C_d L³) ≤ volume(⋃ Y_T)`

under88δ≤rθ,0<r,θ≤1, actual positive angle, separated bristles, actual crossing points, measurable shadings and mass≥λδ^(d−1)/L. It assumes neither bounded physical location nor far-from-stem shading nor retained shading mass. All are derived.

The final theorem audit reports only `propext`, `Classical.choice`, and `Quot.sound`. Compilation is clean; no custom axioms or `sorry`.
