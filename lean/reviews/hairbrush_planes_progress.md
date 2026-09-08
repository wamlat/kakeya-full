# Actual stem-plane binning and overlap checkpoint

`EuclideanSplit.lean` contains 22 proved theorems and 6 definitions. `HairbrushPlanes.lean` contains 21 proved theorems and 3 definitions. Both compile cleanly and have built `.olean` files. The main plane-overlap and bristle-bin theorems audit with only Lean's standard `propext`, `Classical.choice`, and `Quot.sound` axioms.

The coordinate module proves Euclidean head/tail Pythagoras, transverse contraction and its isometric inverse embedding. An actual Householder reflection takes any unit stem direction to the first coordinate axis, and an orthogonal transverse map extends to one fixing the stem. Thus the coordinate frame is available for any actual stem, not a favorable-direction assumption.

A `plank` is defined by its actual transverse-coordinate distance to a line. `plank_iff_affine_plane` proves equivalence to distance at most the stated width from an actual affine plane spanned by the stem and the given transverse vector. The transverse radius is proved equal to the distance to a closest stem point and below distance to every stem point.

`bristle_in_stem_plank` derives containment of every actual bristle carrier meeting the actual stem in a plane plank of width 3δ. Actual projective transversality gives a nonzero transverse vector and hence a unit plane representative. No planar-containment hypothesis is inserted. `bristle_plane_bins` constructs a finite δ-separated net of those actual plane representatives using the proved finite-net theorem; every bristle in a prescribed ball lies in its assigned net plank of width (6+R)δ.

For actual ambient dimension d=k+2, `plane_bin_overlap` proves that at a point of transverse distance at least s, the number of δ-separated unit-normal planks of thickness Cδ containing that point is at most packingConstant(k)*(4C/s)^k, assuming 0<s≤1, C≥1 and 2Cδ≤s. This is exactly the ambient-minus-two exponent in the geometric overlap step behind (4.12). It is proved by deriving a projective cap for the plane representatives in the actual transverse Euclidean space and invoking the proved sphere packing theorem. It does not assert that the original tube directions live in that smaller space.

The finite-measure union consequence of bounded plank overlap is not yet assembled here. The separate forthcoming `ThickCircle.lean` supplies the one-dimensional tangential direction count for (4.13). No claim is made here that the full hairbrush estimate has been proved.
