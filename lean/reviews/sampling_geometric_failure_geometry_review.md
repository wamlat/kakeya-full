# Separate review of the geometric sampling failure budget

Read the complete frozen `SamplingGeometricFailure.lean` at SHA `07595d2c6c00d116c24afa4a4ee0bca5eeb3576f25463c7ebd78d5589fc54ecc`. This agrees with the supplied frozen hash. No mathematical, event-identification or quantifier-order defect was found. The review is read-only; the parent owns compilation and the exact-source audit.

The `law` definition is the same actual `coupledLaw (flatten p) (flatten q)` used by `SphereNetFailure.law`, with the same original nested probability arrays and explicit finite outcome instances. No event probability is supplied in `probability_le`.

The density branch of `bad` is the union of `fullTubeCount <= fullMean/2` and `2*fullMean <= fullTubeCount`. The ball branch is `cutoff <= fullBallCount`. These non-strict failures enlarge the strict source failures. Their complement therefore supplies the source broad density band and the required ball upper bound. It does not supply the stronger narrow `[2*mean/3,4*mean/3]` band used by a different existing realization record, and the source does not claim it does.

Each density branch is matched to the actual finite-product concentration theorem with bound `2*exp(-mean/12)`. Each ball branch is matched to the actual finite-product upper-tail theorem with bound `exp(-cutoff/4)`, using the explicit mean condition `4*ballMean <= cutoff`. The masks count the original full selections on the same tube-cell outcome. A finite union bound over `T ⊕ (T × B)` gives exactly the stated budget; no independence between overlapping tests is used.

The uniform budget multiplies the separate tube and tube-ball cardinalities by their corresponding decreasing exponential bounds. Real powers `u,v` may have either sign. Positivity of `cf,cb,eta,phi` is explicit and is precisely what the stretched exponential limits need. The threshold is fixed before the finite index types, their instances, probability arrays, masks, cutoffs and actual counts. The fixed cardinality coefficients are retained. They need not separately be assumed nonnegative: the generic real limit statement holds for all fixed coefficients, and feasible cardinality upper bounds already constrain them at positive scales.

Empty index families cause no undefined division or artificial positive-population premise. The actual physical application must still derive its count and expected-mean hypotheses and its two positive growth exponents; the generic theorem honestly leaves those inputs explicit. The separate angular event and the final joint success probability are outside this module, as stated.

No source, registry, verifier, lakefile or published checkpoint was modified.
