# Actual measurable unit-segment selection

AnisotropicShading.lean completes the exact-measure carrier-selection interface. In ambient dimension k+1, an original unit tube whose direction lies in an angular*tau cap has its exact affine image carrier covered by N=ceil(1+angular)+1 explicit unit carriers. For each original tube separately, the code takes the finite maximum of the actual real volumes

normalizeBox u tau q '' Y ∩ transformedTube_j.carrier(width*delta/tau), j<N.

The selected j is an actual finite maximum; no desired large subset or partition is assumed. The selected set is measurable when Y is measurable, is finite in measure, lies in its actual selected unit carrier, and lies in the exact image of Y. Finite subadditivity proves selected mass≥volume(Y)/(tau^k*N). For angular=3, the loss is five. One unit carrier is selected per original tube, so the original indexing and transformed direction count remain intact; no duplicate parallel directions are created.

For any finite original family with finite individual measures, the union of all independently selected sets lies in the single common affine image of the original union. Thus selected union volume≤original union volume/tau^k exactly, without an isotropic-grid inflation factor. The finite maximum is allowed to choose an empty set when Y is empty; it does not assert positive mass without a positive original-mass premise.

The selected subsets need not individually preserve the original pointwise broadness or two-ends coefficient merely by inclusion. Exact images have those properties from AnisotropicTransport, and the separate measurable density/marked-broadness recovery step can compare the selected subsets against those full image references.

Lean4.33.1; Mathlib commit0df444a360eaa60ab8c11dca51a86af692955474. Clean .olean build from audit_work/formalization; all12 theorem declarations in the full-source anisotropic_shading_axioms.lean/log audit have dependencies contained in propext, Classical.choice, Quot.sound. No sorry/custom axioms.
