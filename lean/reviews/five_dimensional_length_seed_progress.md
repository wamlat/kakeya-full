# Cap-free five-dimensional original-length seed

`FiveDimensionalLengthSeed.lean` is frozen, clean-compiled and exact-source audited PASS. SHA256: `f33ecf1b83994d21a25f32d0c31cd822f0471784d523b01b0c6a3976b9d3a1e3`.

Both named theorems and both local declarations passed the production all-declaration audit on the exact complete source. Their dependencies use only standard axioms; there are no custom axioms, sorry/admit/native_decide, warnings or errors. Audit details: `five_dimensional_length_seed_audit.json`; raw transcript: `FiveDimensionalLengthSeed_SourceAudit.log`.

`discrete_seed` specializes the already proved unrestricted fractional seed to ambient dimension five and cap exponent m=4, giving actual DiscreteEstimate 5 4 (7/2) (7/2). This theorem uses the constructive full-range fractional seed; it does not import a new Wolff axiom or posit a five-dimensional estimate as an input.

`original_length_bound` has the following scope. Given a fixed Normalization geom, fixed upperLength, fixed positive row coefficient crow, and epsilon>0, it chooses c>0 BEFORE every actual family H:TubeFamily 5 M, individual axis lengths, mesh delta or density lambda. Assuming 0<delta<=1, lambda>0, lengths_i<=upperLength, actual original lengthCarrier incidence at width geom.width*delta, direction separation geom.separation*delta, base bound geom.radius, and each original row cardinality at least crow*lambda/delta, it proves

    c*delta^(1/2+epsilon)*lambda^(7/2)*M <= card(original unionCells).

There is NO cap coefficient or cap-bound premise. The proof derives H.CapBound delta 4 A0 from the actual separated unit directions, with A0=fullDirectionCoefficient 4 geom.separation>=1. It invokes the already proved original-length lower-density adapter at that fixed cap coefficient and absorbs A0^(-1) into the constant. Thus A0 depends only on the fixed separation geometry, not on delta, H, M, lengths, lambda or the original seven-dimensional cap coefficient used elsewhere in the Gaussian route.

There is also NO two-ends assumption, upper row-density bound, lambda<=1 restriction, selected output, or projected-count premise. The lower-density and common-length normalization are actual previously proved constructions. The original row labels and finite union in the conclusion are unchanged. A positive lower length is unnecessary for this finite-cell statement: positive lower row count and actual carrier incidence already rule out empty negative-length rows in any nonempty admissible input, while M=0 is covered directly by the general adapter.

The exact scalar scale exponent is 4-7/2+epsilon=1/2+epsilon. In the intended projected-family application, upperLength=20, the width and base bound are the actual fixed projected geometric constants, the separation is 2/pi, and crow is the inverse of the proved original-to-target fiber constant. These are all fixed before configurations. Combining this theorem with actual projected row and union counts supplies the five-dimensional input for the source Lemma 2.1 route at combined.txt lines255–266. The Gaussian subfamily population and final logarithmic absorption are separate subsequent assembly; this file does not assume them.

Commands in `audit_work/formalization` with the pinned matching Lean/mathlib dependencies:

```sh
lake env lean -o .lake/build/lib/lean/FiveDimensionalLengthSeed.olean FiveDimensionalLengthSeed.lean
python3 ../audit_five_dimensional_length_seed.py
```

The module remains outside the frozen registry until the parent's next integrated publication. The read-only review of the preceding actual Gaussian separated selection is saved separately in `gaussian_projected_selection_scalar_review.md`.
