# Independent scalar review of the actual variable-length maximal operator

No substantive mathematical defect was found. I read all four final modules end-to-end and checked the underlying actual carrier-volume normalization statements already independently reviewed. This was read-only; the geometry agent owns compilation and exact-source audits.

Final reviewed SHA256:

- `DilationIntegral.lean`: `1ae4d332ceb69f7524c7d40af43a199c14fe649c35cf79802eb53c20dc66f308`
- `LengthOperatorGeometry.lean`: `eebfef86494249e681d614a6908795742c6a0d9fc270585a3741190ad0aade5b`
- `LengthOperatorBound.lean`: `68813cf9030002d122665aae0a977f8fd8c47eac26c548da3042699c2486d02b`
- `LengthOperatorNorm.lean`: `e45b94338ec243e8613ab2dc8afce92e9ba8c0a77092f8111e01ac9d0f348574`

The operator is literally the supremum over every base position and every axis length in the fixed closed interval [lower,upper]. Each average integrates the input over the actual variable-length radius-width*delta carrier and divides by that carrier's actual ENNReal Lebesgue volume. It is neither a unit-volume proxy nor an operator introduced through a desired norm predicate. No bounded-position restriction is present.

`DilationIntegral` uses the genuine measurable equivalence x->W*x for W>0. Its pushforward is W^(-n) times volume, so the integral of f(W*x) and its eLpNorm acquire W^(-n) and W^(-n/a), respectively. Both the whole-space and set integral identities use the measurable-embedding transport theorem; arbitrary ENNReal inputs and infinite integrals are covered. The norm identity requires a>0, hence the finite positive exponent in the eLpNorm measure-scaling formula is valid. Quasi-measure preservation derives a.e.-measurability of the dilated input; no unsupported pointwise representative equality is needed.

The per-length exact average identity rescales by that actual positive length: the original finite carrier becomes a unit carrier of radius width*delta/length, base b/length, and input f(length*x). Its numerator and denominator carry the same finite positive factor length^(-n), which is cancelled by the appropriate ENNReal identity. This per-length identity is used for measurability. The final norm bound instead uses ONE common W=max(1,upper,width), avoiding an input or norm constant that varies inside the length supremum.

For each fixed positive length and base, the exact average identity reduces direction measurability to the previously proved lower semicontinuity of actual unit-tube averages. The arbitrary supremum over all bases and lengths is then lower semicontinuous for measurable nonnegative inputs. For a.e.-measurable inputs, the actual averages are unchanged on every restricted carrier by null-set changes, yielding pointwise equality of the whole supremum to a measurable representative's supremum. Thus output measurability is derived despite the uncountable position/length parameter set; it is not assumed or obtained from an unjustified countable-supremum argument.

With h=min(1,lower,width)>0, the previously proved actual contained-carrier bound gives V_actual>=h^n*V_unit. After the common contraction by W, the numerator is at most the numerator over the containing actual unit carrier, while the denominator is at least (h/W)^n*V_unit. The direction of both inequalities in ENNReal.div_le_div is correct. The constant that remains in pointwise domination is (W/h)^n. All cancellations involve finite positive geometric scaling coefficients. The pointwise theorem also permits delta=0 consistently, while the final operator norm theorem requires 0<delta<=1.

`LengthOperatorNorm.from_unit` applies the already proved real unit-operator theorem to g(x)=norm(f(W*x)). This is valid for any a.e.-measurable input taking values in a normed additive group with its Borel measurable structure, including real and complex inputs; only its scalar norm is used. The equality eLpNorm(norm f)=eLpNorm(f) and the exact dilation identity give the fixed factor

    (W/h)^n * W^(-n/a).

The scale exponent remains exactly 1-n/a-epsilon, and there is no new delta, input, or length-dependent exponent error. The positive constant is chosen after fixed a, length interval, width and epsilon, before delta, input space, or input function. Finite input norm and finite output values are not silently assumed; the inequalities are in ENNReal and include the infinite-norm cases.

The interval upper bound need not be separately declared positive: if a permitted length exists, it is at least the fixed positive lower bound. If the fixed interval is empty, the length supremum is zero, consistently covered. This does not exclude the intended nonempty fixed-length regime. The endpoint wrappers establish positive exponent a before applying the generic adapter and preserve the exact radical formulas and first six-dimensional step.

These modules close the actual fixed-variable-length, fixed-width norm-operator normalization, not just the previously proved shading inequality. The output uses actual original carrier-volume denominators, arbitrary positions, the complete permitted length interval and the literal spherical eLpNorm. This review found no hidden volume-comparison, output-measurability, norm, or normalized-operator oracle in the final from_unit theorem; its sole analytic input is the already proved actual unit-operator estimate.
