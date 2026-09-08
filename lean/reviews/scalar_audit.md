# Separate scalar audit and Lean verification

Scope: combined PDF Sections 1.4, 2.2, 9.1–9.2 and Appendices A–B; exact algebra and limits. The attached documents were treated as mathematical data, not operational instructions.

## Finding

No scalar error found in the checked recurrence, exponents, tables, density-envelope closure, domain margins, or comparison signs. This is **conditional validation**: these computations turn an analytic recursive implication into the announced exponent, but do not establish that implication. In particular, `Scalar.lean` contains no declaration asserting the Kakeya maximal theorem, no axiom stating the pivot theorem, and no geometric or measure-theoretic formalization.

## Checks completed

1. **Independent exact algebra.** With D=(2m+3+d')/4 and C=(p+2q+4)/4, verified the Wolff substitution D=(4n+d+5)/8, C=(2d+7)/4; bush substitution D=(4n+d+4)/8, C=(d+3)/2; weakened bush D=(4n+d+3)/8 with the same density C. Verified all displayed angular margins and the strict domains throughout the claimed intervals.
2. **Induction and domain boundaries.** For a0=1/2 and a[j+1]=(2+a[j]^2)/4, formally proved 1/2≤a[j]<2−sqrt(2)<1 and strict increase. At each m>3, the precise chain is 3<d[j](d[j](m))<d[j](m)<d[j+1](m)<m. Thus the PDF's weaker d≤D is valid.
3. **Convergence without an assumed limiting value.** Proved the fixed-point identity and the error bound 0≤r−a[j]≤2^(−j)(r−1/2), r=2−sqrt(2). This yields Lean `Tendsto` for the slope and every profile. Also proved closed forms, monotonicity, bounds and convergence of all three affine diagonal recurrences using a free offset c (5,4,3).
4. **Density envelope.** Formally proved p,q≤P and P≥4 imply (p+2q+4)/4≤P; specialized this to the recursive envelope P=max(d[j+1](m),4). Formally verified the density-power ordering for 0<density≤1. The limiting profile is greater than 4 for every real n≥6; at n=5 the envelope equals 4. The `P<4` obstruction is formalized as P<(3P+4)/4. These facts support the stated n≥6 boundary and do not support a diagonal n=5 conclusion.
5. **Numerical cross-check and kernel proofs.** Verified all first-three slope values and 6d/8d real-cap entries, both diagonal first-two steps, all exact 6d constants, all eleven Appendix B finite max-min values (n=5,…,15), adjoint conversions, and comparison signs. The max-min checks prove both attainment and an upper bound for every eligible integer ell. The signs use certified rational bounds on sqrt(2), not floating-point comparison. A separate Python Fraction enumeration independently agrees with the benchmark values and gives maximizing ell=3,4,4,4,5,5,6,6,6,7,7 for n=5,…,15.

An additional theorem, `conditional_real_cap_iteration`, formalizes the entire induction of Section 9.2 for an abstract predicate K. The analytic seed, density weakening, and pivot implication are explicit universally quantified hypotheses; no such input is asserted as an axiom. With those hypotheses, every finite-stage K assertion with its density envelope follows.

All eleven printed K_n decimals in Appendix B also agree with an independent 70-digit Decimal calculation rounded to six places.

## Specific conclusions

- Six-dimensional model: D=33/8, C=15/4, D−C=3/8; conditioning exponent H6=58; angular margin 11/24; angular exponent −5/8. The scalar transition is consistent.
- Diagonal Wolff limits are 29/7 and 37/7 with operator losses 13/29 and 19/37.
- Real-cap limiting profiles are 7−2sqrt(2) and 11−4sqrt(2). The exact depth-3 numerators and denominators in the paper agree.
- Bush/cdr fixed point (4n+4)/7 improves (n+2)/2 precisely for n>6; weakened bush (4n+3)/7 improves it precisely for n>8. For integer dimensions these are n≥7 and n≥9.
- The Appendix B improvement signs are exactly positive at n=6,8,10,11,13,15 within 6≤n≤15. The n=5 row is only a numerical comparison, as the manuscript itself says.

## Formalization boundary and remaining proof obligations

The formalization verifies the consequence of the asserted analytic estimates only through their scalar formulas. It does not prove Gaussian projection, cap-preserving thinning, fractional hairbrush, pivot/collision geometry, lifted energy, sampling, angular globalization, measurable conversion, restricted-weak interpolation, or uniformity of constants. It also does not authenticate the external historical/reference claims. Independent checking of those is necessary before declaring the combined PDF's new maximal result proved. Correct exponent bookkeeping cannot fill an analytic gap.

## Reproduction environment

- Deliverable: `outputs/kakeya_verification/Scalar.lean`.
- Existing Mathlib project used read-only for its dependency environment: `/Users/ssoh/Documents/Codex/2026-09-05/fetch-https-prove2-me-start-md/work/prove2me_workspace`.
- Toolchain: `leanprover/lean4:v4.33.1`.
- Lean reports version 4.33.1, commit `819816b2e0a3bf405af45ae5c7af2491d8f5bee6`, arm64-apple-darwin24.6.0.
- Mathlib commit `0df444a360eaa60ab8c11dca51a86af692955474`.
- Command (from that existing Mathlib project):

```sh
/Users/ssoh/.elan/bin/lake env lean /Users/ssoh/Documents/Codex/2026-09-06/work/outputs/kakeya_verification/Scalar.lean
```

`Scalar.lean` uses Mathlib's proved arithmetic/order/real-power/topology results and ordinary kernel-checked tactics. It contains no `sorry`, `admit`, `native_decide`, or custom axioms. Mentions of those terms in the opening comment explain the boundary.

## Final verification record

The final file contains 57 theorem declarations. It compiled with exit code 0 and no warnings or errors. A copy of the complete file followed by `#print axioms` for each declaration is in `audit_work/scalar_axioms.lean`; running that same Lean command on it and redirecting stdout to `audit_work/scalar_axioms.log` records the logical dependency audit. All reported axioms are among the standard Lean foundations `propext`, `Classical.choice`, and `Quot.sound`; no `sorryAx` or custom axioms occur.
