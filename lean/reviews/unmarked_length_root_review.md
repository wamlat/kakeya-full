# Independent review of unmarked source length adapters

Read UnmarkedLengthEstimates.lean and SourceUnmarkedLengths.lean completely at final audited hashes 9a2ceb7a87aa23d7b86491124c777ef6756baa6b9ab5d6a1e91c99e1275984fe and 1fad383899933828f56fb22a0e9e4576fdf6adabdb50aa05159de83459c03217. No defect found.

The common fixed W=max(1,lengthUpper) changes physical bases, mesh and density together, preserving the original integer labels/union and each old row. The source lower ratio is unchanged. B*W is legal after first weakening the actual ball exponent to min(alpha,1); since radii are at most one, exponent weakening has the correct direction. Thus alpha is any positive fixed number in the public theorem. The positive scalar W^[-(m-D+eps)] W^(-C) depends only on parameters fixed before configuration, including eps; no original scale/density/population enters it. The actual normalized width/separation and radius/W are proved by existing geometric lemmas.

The source angular wrapper uses only the stated Base/Lifted inputs, positive p and source pivot/margin ranges; it preserves the original full-two-ends premise. The globalization wrapper accepts only the source TwoEnds implication and returns an unrestricted original-count conclusion with max(D,C), no original two-ends or upper-density premise. A positive lower length bound is unnecessary for these stronger original-cardinality inequalities. Neither theorem claims an actual variable-tube-volume maximal bound; that separate ratio adapter remains geometry work.

Exact-source audit: unmarked_length_audit.json PASS, 7 named /15 local theorem /17 all-local declarations, standard foundations only.
