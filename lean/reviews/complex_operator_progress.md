# Complex-input maximal operator extension

ComplexOperator.lean compiles cleanly. It defines the actual same-tube maximal operator by the nonnegative integrand ENNReal.ofReal(norm(f(x))) for complex inputs. The actual original-position supremum and carrier-volume denominators are unchanged.

The exact identity with the real-input normMaximal applied to the real norm function is proved pointwise. For any a.e.-measurable complex function, its real norm is a.e.-measurable, and Mathlib eLpNorm_norm identifies the real norm-function input norm with the original complex input norm. Applying the already proved real theorem therefore keeps precisely the same constant and scale exponent. It does not assume a new interpolation or geometric estimate.

Public corollaries cover 33/8 in dimension six, the all-dimensional endpoint and profile formulas, the exact six/eight radicals and both rational diagonal limits. This makes the conventional complex-valued interpretation of the source absolute-average operator explicit. These are new development sources outside checkpoint20. The individual exact-source audit passes for SHA256 173adb29079b8fa60f45022043df4978a4c468cf5fe07a928c44617d973db99a: 14 local theorem declarations and 16 all-local declarations, depending only on propext, Classical.choice and Quot.sound. Independent review passes; see complex_operator_geometry_review.md.
