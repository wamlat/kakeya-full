# Independent scalar review of the entire-sphere projective net

No substantive mathematical defect was found. I read the complete final `ProjectiveSphereNet.lean`, including its finite-index wrapper, and checked its actual projective packing and triangle interfaces. This was read-only; the geometry agent owns the source audit.

Final reviewed SHA256: `9417c061c19cb7675e20474f1aab27e2d46a63ce10fcd5d295bc273beb5308ef` (confirmed frozen and clean by its owner).

The packing theorem applies to every finite separated set of actual unit vectors in ambient dimension k+1. Their projective distance to the zero vector is exactly one, so the already proved dimension-reduced cap packing theorem supplies the genuine C_k*rho^(-k) cardinality bound for 0<rho<=1. The center zero is allowed by that packing theorem; no false unit-center premise is bypassed. The exponent is k, not the ambient k+1.

The net construction maximizes cardinality among ALL finite rho-separated unit-vector sets, using the actual packing bound to place every possible cardinality below one finite natural ceiling. The empty set establishes a valid cardinality-zero candidate. Nat.findGreatest therefore supplies an actual finite set of maximum possible cardinality, not an assumed sphere covering or a maximum inside one prechosen tube family.

If an arbitrary unit vector were not within strict distance rho of any chosen point, it would be rho-separated from every chosen point. Positive rho and zero self-distance show it is not already present. Inserting it preserves unit norms and actual projective separation and increases cardinality by one, contradicting the maximum while remaining under the proved global packing ceiling. This proves strict coverage of the ENTIRE sphere. Antipodal representatives cause no issue: their projective distance is zero, so a positive-separated set cannot contain both, and either representative is already covered in the same projective direction.

The cap-containment theorem chooses a net center within strict rho of the arbitrary original unit center, then applies the actual projective triangle inequality. Thus a closed radius-r original cap lies in an open radius-(rho+r) net cap, in particular every closed rho cap lies in one open 2rho cap. The tested vector itself need not be unit for this triangle argument, as the actual min(norm(v-w),norm(v+w)) triangle bound is valid on the ambient vector space. Strict and closed endpoint conventions are preserved exactly.

The indexed wrapper is an actual enumeration of the same finite set by its finite equivalence. Injectivity, unit norm, separation, coverage and double-cap containment are all transported from that same constructed net without changing its cardinality bound. The k=0 case is included: ambient dimension is still one, the projective sphere is nonempty, and the proof and packing exponent zero remain meaningful.

The Net record contains its geometric properties, but exists_net and exists_indexed_net actually prove and construct them; the final existence theorem does not assume a net count or cover. This supplies the geometric whole-sphere test set needed for source (6.19). Its theta-to-N cardinality budget and the probability union bound are separate downstream conclusions; the file makes no hidden probability or scale-threshold assumption.
