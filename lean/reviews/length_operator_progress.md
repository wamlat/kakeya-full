# Actual variable-length maximal operator

The four new modules are frozen and compile cleanly. Exact-source all-local-declaration audits pass for24 named source theorems,36 local theorem declarations and42 local declarations total, using only propext, Classical.choice and Quot.sound. They are outside frozen checkpoint20 until a later integrated snapshot. No existing source, lakefile, verifier, registry or published output was changed.

The operator is concrete: LengthOperatorGeometry.average integrates the nonnegative input over SamplingGeometry.lengthCarrier(tube v b) ell(width*delta), then divides by the measure of THAT actual carrier. LengthOperatorGeometry.maximal takes the extended supremum over EVERY original base b and EVERY ell in the fixed interval[lower,upper]. It does not substitute the containing unit tube volume into the definition and does not assume a norm or volume comparison.

DilationIntegral builds the actual measurable equivalence x↦W*x with inverse x↦x/W, proves its Lebesgue pushforward as ofReal(W^(-n))*volume, and derives exact global and set nonnegative integrals. Its eLpNorm formula is ||f(W·)||_a=W^(-n/a)||f||_a for every a>0, with arbitrary input/output integral sizes. It also proves actual null-set-preserving transport of a.e.-measurable inputs. No finite-integral assumption is hidden in a conversion to real numbers.

Measurability of the uncountable supremum is proved independently of its upper bound. For each ell>0, the actual ell-length average is IDENTICAL to the ordinary unit-length average at radius width*delta/ell, with input f(ell·) and base b/ell. This uses exact set and measure scaling. Each fixed-length/base average is lower semicontinuous in direction by the proved unit-average theorem. Arbitrary suprema preserve this property. A global a.e. input change preserves every original tube integral, hence a.e.-measurable inputs have measurable outputs too. The zero/empty interval case is included by the extended supremum convention.

LengthOperatorBound proves the actual pointwise comparison using h=min(1,lower,width)>0 and W=max(1,upper,width):

    T_lengths,delta f(v) <= (W/h)^n T_unit,delta(f(W·))(v).

The numerator bound is actual containment under the SAME common dilation. The denominator lower bound is the contained-carrier inequality already proved by LengthTubeVolume. It is not an expected-volume bound or an assumed density normalization. Delta and the direction sphere are unchanged, and the supremum ranges over all original positions.

LengthOperatorNorm.from_unit composes this pointwise bound with exact norm scaling. Its fixed coefficient multiplier is

    (W/h)^n * W^(-n/a).

The public Estimate predicate fixes lower,upper,width and epsilon BEFORE choosing C, and C precedes delta and every input. The output is the actual Mathlib eLpNorm with the original sphere measure and exact source loss delta^(1-n/a-epsilon). Inputs range over a.e.-measurable functions into any normed additive commutative group with its Borel measurable structure, including real and complex inputs; taking the input norm reduces to the already proved real operator without changing constants. Infinite input norms are handled in ENNReal. All0<delta<=1 and all epsilon>0 are included.

Concrete endpoint wrappers expose the main formula in every integer dimension n>=6, its equivalent limitProfile expression, 33/8 in dimension6, and the exact dimension6/dimension8 limit values7-2sqrt2 and11-4sqrt2. These invoke the proved unit operator, whose geometric and interpolation premises are discharged. No published external axiom, operator law, conditional sampling event, norm scaling or desired operator bound is an input.

Scope: a fixed positive lower length and width and a fixed finite upper length are necessary normalization parameters for this theorem. Constants are not asserted uniform as the lower bound or width tends to zero. Lengths vary freely INSIDE the operator supremum; this is stronger than merely evaluating different lengths on a supplied finite family. The already published standard unit operator is unchanged. Independent read-only review of the four final sources was requested from the scalar agent. The exact audit record is length_operator_audit.json; validation uses Lean4.33.1 and pinned mathlib0df444a360eaa60ab8c11dca51a86af692955474.

| Module | Named source theorems | Local theorems | All local declarations | SHA-256 |
|---|---:|---:|---:|---|
| DilationIntegral | 6 | 10 | 11 | 1ae4d332ceb69f7524c7d40af43a199c14fe649c35cf79802eb53c20dc66f308 |
| LengthOperatorGeometry | 7 | 10 | 12 | eebfef86494249e681d614a6908795742c6a0d9fc270585a3741190ad0aade5b |
| LengthOperatorBound | 3 | 3 | 3 | 68813cf9030002d122665aae0a977f8fd8c47eac26c548da3042699c2486d02b |
| LengthOperatorNorm | 8 | 13 | 16 | e45b94338ec243e8613ab2dc8afce92e9ba8c0a77092f8111e01ac9d0f348574 |
