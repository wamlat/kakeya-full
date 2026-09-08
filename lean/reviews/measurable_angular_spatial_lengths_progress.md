# Variable-length measurable angular-spatial decomposition

The new sources `SpatialTubeLengths.lean` and `MeasurableAngularSpatialLengths.lean` are frozen and compile cleanly with zero diagnostics. Exact-source full-environment audits PASS with only standard Lean foundations: propext, Classical.choice and Quot.sound. Every local declaration was inspected, including proof-bearing definitions and generated record declarations. No custom axiom, sorry or diagnostics occurs. These files are separate from the frozen checkpoint20 sources.

Let U=max(1,upperLength) and Wcover=width+3U. The actual per-tube axis length can vary arbitrarily below upperLength; a positive lower length is not required. Every original lengthCarrier in a 3*tau cap is contained in its SAME original transverse/longitudinal lattice label's finite box of half-length 2+Wcover and transverse radius (k+Wcover+3)*tau in ambient k+1. A direct norm/axis-parameter proof establishes this; no homothety changes original locations, directions, scale or shadings. The box is contained in an explicitly constructed finite tube of length 2*(2+Wcover).

The measurable adapter keeps the original weighted angular object, its actual compressed original indices, and the concrete same-index spatial labels. It uses the existing proportional spatial filter with Csp=spatialConstant(k,Wcover). Actual lattice counts prove that filter’s hypothesis. Summed original shading mass retains the same 3/4 spatial factor, hence the SAME positive c_k*log(2/delta)^(-3) lower bound. Full original length carriers, not merely retained shading points, have the finite containing-tube field. Actual occupied output unions have overlap at most 2*Csp*tau^(-beta); broadness error is 64*Cang*Csp, uniform over beta in [0,1].

All original-index disjointness, injectivity, exact tube identities, measurable and finite retained sets, individual original-shading inclusion, original-union containment, and inherited original direction separation are literally the frozen MeasurableAngularSpatial definitions/theorems evaluated at Wcover. The output record carries the new length-aware containing box/tube fields explicitly. No per-tube density, two-ends, cap-packing premise on the original family, bounded-position condition, desired count, retained mass, broadness, or analytic estimate is supplied.

`construct` creates its angular pieces internally and includes empty families. Constants depend only on ambient dimension, fixed width and fixed upper length, preceding delta, beta, every original axis length, all positions/directions, all shadings and population. The source fixed comparable length range is therefore included. This closes the measurable angular-plus-spatial assertions of Lemma3.2 under that full fixed geometry convention. The discrete old-cell-constant assertion remains attributed to its separate finite construction, not inferred from a bare measurable output record.

Frozen hashes:

- SpatialTubeLengths: 7fd29ea3872f1301975f82261c1fdcf89084c7324dd4481f36d15943b7933635
- MeasurableAngularSpatialLengths: fbc9188f6ddfb3884f5b9c1e068f1ef6d7f8a4aee3be74b36f3fea0e1dcedb92

Final audit inventory:

- `SpatialTubeLengths`: 2 source theorems, 1 definitions, 0 structures; 5 local declarations / 4 local theorems, PASS. Exact-source logs and JSON are `SpatialTubeLengths_axioms.log` and `SpatialTubeLengths_audit.json` in audit_work.
- `MeasurableAngularSpatialLengths`: 7 source theorems, 0 definitions, 1 structures; 29 local declarations / 16 local theorems, PASS. Exact-source logs and JSON are `MeasurableAngularSpatialLengths_axioms.log` and `MeasurableAngularSpatialLengths_audit.json` in audit_work.
