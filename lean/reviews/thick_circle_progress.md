# Thick great-circle cap packing

`formalization/ThickCircle.lean` compiles cleanly and its `.olean` is built. The main `plane_bin_direction_count` audit reports only `propext`, `Classical.choice`, and `Quot.sound`.

The file proves actual finite packing in a great-circle strip in ambient dimension d=k+2. On a positive coordinate chart, its injective grid label has one tangential coordinate controlled by cap radius ψ and k normal coordinates controlled by width Wδ. An actual anisotropic integer box therefore counts the labels, giving O_k((1+W)^k ψ/δ). Four signed tangential charts cover every unit vector at normal distance at most 1/2 from the coordinate plane. Actual antipodal representative selection transfers ordinary spherical-cap counting to projective caps, and actual direction separation supplies index-map injectivity.

The complete `indexed_thick_circle_count` assumes actual unit vectors, actual projective δ-separation, actual cap membership at radius ψ≥δ, and actual Euclidean normal thickness ≤Wδ, with W≥0 and Wδ≤1/2. It concludes cardinality≤circleConstant(k,W) ψ/δ, where circleConstant=4(4Q+5)(4QW+5)^k and Q=chartConstant(k+1,1/2)=3(k+2). No planar-counting assertion appears as a hypothesis.

The file then constructs an orthogonal straightening map from the actual stem frame and the selected unit plane representative. `assigned_direction_thin` proves that assigning the bristle's actual transverse normal to a δ-near plane representative implies full-direction normal thickness at most δ. Its proof has no inverse-transversality factor: transverse speed is at most one. `plane_bin_direction_count` derives the O_k(ψ/δ) bound for actual tube directions in a plane bin, at δ≤1/2.

This is the geometric counting step used in (4.13). The generic W dependence also supplies the packing component of (5.17) when W=O(κ⁻¹), giving the correct κ^(−(d−2)) factor; the separate geometric assertion that collision directions lie in that strip still needs formal assembly. The dyadic inverse-angle sum and actual intersection row energy are the next module, PlanarEnergy. Coarse scales where Wδ>1/2 are explicitly outside this theorem and have not silently been covered.
