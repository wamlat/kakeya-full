# Actual operator measurability and open carriers

The sources `TubeOpenCarrier`, `ParameterLIntegral`, and
`KakeyaOperatorMeasurability` compile without diagnostics and pass an exact-source
audit of every local declaration. All dependencies are standard Lean
foundations; there is no custom-axiom dependency.

`TubeOpenCarrier` identifies the actual positive-radius closed capsule with
the closure of the open capsule. Both sets are convex, so their frontiers have
zero ambient volume. The resulting a.e. equality preserves actual carrier
measure and the integral of every nonnegative extended-real function. Membership
in the open capsule is open jointly in its base and direction.

`ParameterLIntegral` proves a general Fatou argument: on a first-countable
parameter space, measurable spatial sections and pointwise lower
semicontinuity in the parameter imply lower semicontinuity of the nonnegative
integral. Applying this to open-set indicators gives the actual jointly lower
semicontinuous tube integrals, without a boundedness or integrability assumption
on the measurable integrand.

`KakeyaOperatorMeasurability` uses the proved exact direction/position-invariant
carrier volume to put the same denominator inside every integral. Every
fixed-base actual average is lower semicontinuous, so its supremum over **all**
Euclidean bases is lower semicontinuous and measurable on the unit sphere.
An a.e.-measurable input also has a literally measurable output: changing to a
measurable representative changes no tube average at any position. The bounded
real indicator supremum and every real indicator level set are measurable.

Exact audited source hashes:

- TubeOpenCarrier: `293bdfaa6917d7477e25a62aee70c07e6cc81323718a8b7ab14c73abd133810a`
- ParameterLIntegral: `1f87ef795080fcf9c5cc0b04a61c8a659fc894d6494ed4b71cd07bb70e56a8f7`
- KakeyaOperatorMeasurability: `410fb421849b0392c1679b8f271f45d08564f0bcf56243206aa7d5f03973935b`

The corresponding `*_operator_audit.json` files record 27, 3 and 10 local
declarations respectively. Independent mathematical reviews are recorded in
`open_carrier_parameter_integral_review.md` and
`operator_measurability_independent_review.md`.

These results establish measurability of the actual operator. They do not assert
the remaining strong-norm interpolation theorem.
