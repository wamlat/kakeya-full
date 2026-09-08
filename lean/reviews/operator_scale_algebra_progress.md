# Uniform operator scale choices

`OperatorScaleAlgebra.lean` compiles without diagnostics and passes an
exact-source audit of all 11 local declarations (7 theorem declarations).
Its frozen source hash is
`6e1a6324ca8aade19dc061687c02c41466788c88687f6f3de672f27e9c743e96`.
Every dependency is a standard foundational axiom.

The earlier `Reduction` module already checked the interpolation identities and existence of a sufficient error budget. This module packages explicit named choices, the stronger epsilon/2 bound, and the final delta-power comparison for direct analytic assembly.

For 1<a<r the file proves 0<theta<1 and the interpolation identity
`1/a=(1-theta)/r+theta`, where `theta=(r-a)/(a(r-1))`. It then proves the exact
combined scale exponent

`(1-theta)(n-a+e)/r+theta(n-1)
 = (n-a)/a+(a-1)(r-a+e)/(a(r-1))`.

For each fixed a>1 and epsilon>0 the actual choices
`r=a+a epsilon/4` and `e=a epsilon/4` are positive and r>a. The entire excess
over (n-a)/a lies strictly between zero and epsilon/2. Consequently its
negative delta power is bounded by `delta^(-(n-a)/a-epsilon)` for every
0<delta<=1. Neither r nor e depends on delta.

These are scalar calculations for the final analytic assembly. They do not
assert either missing strong interpolation theorem or an operator norm bound.
