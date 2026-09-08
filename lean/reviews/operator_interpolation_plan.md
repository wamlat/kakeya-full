# Section 9.3 operator interpolation: exact next formalization

Read-only audit of combined PDF §9.3, equations (9.7)–(9.8), and the pinned Mathlib sources. No Lean source or frozen package was edited for this task. The statements below are proposed next theorems and independently checked mathematical derivations, not newly kernel-checked interpolation theorems.

## Finding

The manuscript's two interpolation steps and final exponent are mathematically consistent for 1<a<infinity. The important missing functional-analytic step is that (9.7) is only an indicator estimate. It is not already weak type(a,a) on all functions. A proof must establish restricted-weak-to-strong interpolation, or a suitable Lorentz-space theorem, before treating general functions.

Searches through the entire pinned Mathlib tree found no Marcinkiewicz, restricted weak type, Lorentz-space, or Riesz–Thorin interpolation theorem. The useful existing ingredients are listed below. The Complex/Hadamard three-lines theorem and ordinary Lp exponent-comparison lemmas do not by themselves supply the missing sublinear-operator interpolation.

The classical distinction and a restricted-weak interpolation theorem are discussed in [Terence Tao's UCLA Math247A notes1, Section8, Theorem8.5](https://www.math.ucla.edu/~tao/247a.1.06f/notes1.pdf). That displayed theorem uses finite input endpoint exponents, so it should not be cited as a verbatim Lean-ready theorem with the input infinity endpoint. The direct truncation/dyadic proof proposed here treats the needed infinity endpoint explicitly and imports no theorem as an axiom.

## Exact quantitative composition

Let T_delta be an actual positive sublinear operator from a measure space(X,mu) to(Y,nu). For the Kakeya application X is Euclidean space and Y is the direction sphere/projective sphere with the chosen finite surface measure. Assume its operator laws, measurability, and the following bounds have been proved for0<delta≤1.

1. Indicator bound: for every fixed e>0, there is A_e>0, chosen before delta,E,t, such that

   `nu{T_delta(1_E)>t} ≤ A_e delta^(-(n-a)-e) t^(-a) mu(E)`

   for measurable E with finite measure and every t>0. The source gives the nontrivial range0<t≤1; the trivial infinity contraction extends the bound to t>1 because the level set is empty.

2. Infinity contraction: for each nonnegative measurable f bounded almost everywhere by b, T_delta f≤b almost everywhere. In particular its L-infinity norm is at most that of f.

3. Strong L1 bound:

   `integral T_delta f dnu ≤ C1 delta^(-(n-1)) integral f dmu`,

   with C1 fixed before delta,f. For the actual maximal operator this follows from the actual tube-volume lower bound, pointwise domination by the full L1 mass, and finite total direction measure. It is not necessary to assume finite nu in the abstract interpolation theorem if this L1 bound is already an input; deriving it geometrically does require the direction-measure finiteness.

The next complete abstract result should conclude, for every epsilon>0, existence of C_epsilon>0 before delta and f such that

`||T_delta f||_a ≤ C_epsilon delta^(-(n-a)/a-epsilon) ||f||_a`.

This remains a theorem about a supplied operator and proved operator laws, not an axiom asserting existence or estimates for the Kakeya operator. The actual K_delta must instantiate every field.

### First stage: indicator-only bound plus infinity

For fixed r>a, set

`gamma=(r-a)/(2a)>0`, `b=a(1+gamma)=(a+r)/2`, `q=2^(-gamma)<1`.

A concrete sufficient strong-r bound, with A denoting the indicator distribution coefficient, is

`integral (Tf)^r dnu ≤ [r*4^r / ((r-b)*(1-q)^a)] * A * integral f^r dmu`.

The constant is finite, positive, and independent of A and the function. Thus the norm coefficient is a fixed C(a,r) times A^(1/r). After A=A_e delta^(-(n-a)-e), this is exactly the source's scale power delta^(-(n-a+e)/r).

Proposed elementary proof:

- First take nonnegative simple f with finite-measure support and its finite dyadic bands E_j={2^j≤f<2^(j+1)}.
- Given t>0 choose an integer J with2^J≤t/4<2^(J+1). The low part j≤J has size≤t/2, so the infinity contraction leaves only the high part j>J.
- Apply finite subadditivity and allocate the high-part output thresholds proportionally to `(1-q) q^(j-J-1)`, whose total over j>J is1.
- The indicator bound and a union bound give

  `nu{Tf>t} ≤ A*4^b/(1-q)^a * sum_{j:t<4*2^j} (2^j/t)^b mu(E_j)`.

- Integrate against r*t^(r-1), interchange the nonnegative finite sum/integral, and evaluate the power integral over0<t<4*2^j. Its denominator is r-b>0. Since f≥2^j on E_j, the stated bound follows.
- Extend to all nonnegative measurable f by a monotone simple approximation and the actual operator's monotone-limit/Fatou property. A finite-sum sublinearity hypothesis alone does not justify this final extension.

This is a suitable first substantial implementation target. It avoids building the entire Lorentz-space interpolation framework and does not replace the indicator hypothesis with a stronger, unproved all-function weak bound.

### Second stage: strong L1 and strong Lr to strong La

For fixed1<a<r, suppose the strong operator norm coefficients are A1>0 and Ar>0. They imply the corresponding weak bounds by Markov. For each t>0 decompose

`f_hi=f*1_{f>c*t}`, `f_lo=f*1_{f≤c*t}`.

Sublinearity and Markov give

`nu{Tf>t} ≤ (2*A1/t) integral_{f>ct} f + (2*Ar/t)^r integral_{f≤ct} f^r`.

Layer cake and Tonelli then yield

`integral(Tf)^a ≤ [2a*A1*c^(1-a)/(a-1) + 2^r*a*Ar^r*c^(r-a)/(r-a)] integral f^a`.

For f in L^a the high part really is in L1 and the low part in Lr, by their pointwise cutoff bounds; these are derived hypotheses, not extra input membership assumptions on f. Taking

`c=(A1/Ar^r)^(1/(r-1))`

gives

`||Tf||_a ≤ [2a/(a-1)+2^r*a/(r-a)]^(1/a) * A1^theta * Ar^(1-theta) * ||f||_a`,

where

`theta=(r-a)/(a*(r-1))`, `0<theta<1`, `1/a=(1-theta)/r+theta`.

This is the precise useful special-case interpolation theorem to implement. It handles the genuinely sublinear maximal operator; directly applying a linear Riesz–Thorin theorem would require an additional justified linearization. Interpolating only the two output norms and then comparing input norms is also insufficient: the usual input log-convexity inequality has the opposite direction from the bound needed here. The input truncation is essential.

### Final scale algebra and uniform choices

With A1=C1 delta^(-(n-1)) and Ar=C(r,e) delta^(-(n-a+e)/r), the resulting positive scale-loss exponent is

`s=(1-theta)*(n-a+e)/r + theta*(n-1)`.

The exact identity is

`s = (n-a)/a + (a-1)*(r-a+e)/(a*(r-1))`.

It exposes the full error without an implicit continuity argument. For any epsilon>0, choose

`r=a+a*epsilon/4`, `e=a*epsilon/4`.

These choices depend only on fixed a,epsilon and precede obtaining A_e, Ar, and every delta or configuration. Then r>a, e>0 and

`0 < s-(n-a)/a < epsilon/2 < epsilon`,

because `(a-1)/(r-1)<1`. The remaining change of delta exponent is monotonicity on0<delta≤1. No delta-dependent r or e, and no uniformity of C(r,e) as r tends to a, is required. Constants may diverge as epsilon tends to0, exactly as permitted by (9.8).

The final scalar lemma can be proved separately with real arithmetic/rpow identities. It must not be mistaken for the currently missing two functional-analytic interpolation steps.

## Suggested formal interfaces

Use extended nonnegative output integrals first, so a possibly infinite maximal supremum is not silently converted to a finite real number. For `T : (X → ENNReal) → (Y → ENNReal)`, the minimal actual-law package should include:

- measurability of T f for measurable f;
- congruence under mu-almost-everywhere equality, with nu-almost-everywhere equality of outputs;
- monotonicity, T0=0, positive homogeneity, and subadditivity for nonnegative measurable functions;
- monotone-limit/Fatou compatibility, sufficient for the simple-function approximation;
- the infinity contraction on almost-everywhere bounded functions.

The restricted distribution estimate and strong-L1 coefficient should be separate quantitative fields, not hidden inside an opaque property called an interpolation hypothesis. For the actual averaging supremum, countable subadditivity or monotone-limit compatibility follows from monotone convergence of each tube integral and exchange of the two suprema; that proof still has to be supplied. Input/output measures should have SFinite instances for the direct Tonelli route (Euclidean volume and a finite direction measure satisfy these).

The principal next statement, in mathematical Lean-style notation, is:

```
restricted_indicator_and_l1_to_strong:
  1<a -> 0<C1 ->
  (forall delta in Ioc(0,1), actual_positive_operator_laws(T_delta)) ->
  (forall e>0, exists Ae>0, forall delta,E,t,
     indicator_tail(T_delta,E,t) <= Ae*delta^(-(n-a)-e)*t^(-a)*mu(E)) ->
  (forall delta,f, integral(T_delta f) <= C1*delta^(-(n-1))*integral f) ->
  forall epsilon>0, exists C>0, forall delta,f,
    (integral (T_delta f)^a)^(1/a) <=
      C*delta^(-(n-a)/a-epsilon)*(integral f^a)^(1/a).
```

All measure/nonnegativity/scale restrictions described above must be explicit in the eventual source. The actual output should additionally state the norm bound using `eLpNorm` and deduce `MemLp`/a.e. finiteness, then connect to the chosen real-valued K_delta representation. This avoids ENNReal.toReal mapping an unproved infinite value to0.

## Pinned Mathlib APIs actually found

Pinned toolchain: Lean4.33.1; mathlib commit `0df444a360eaa60ab8c11dca51a86af692955474`. Paths below are relative to `.lake/packages/mathlib/Mathlib/` in the development project. These APIs were read from source; the proposed theorem interfaces above have not been compiled.

| Ingredient | Existing API and exact location |
|---|---|
| Power layer cake with strict levels | `MeasureTheory.lintegral_rpow_eq_lintegral_meas_lt_mul`, `Analysis/SpecialFunctions/Pow/Integral.lean:91`; input real nonnegative a.e. f, AEMeasurable f, real p>0 |
| General strict layer cake | `lintegral_comp_eq_lintegral_meas_lt_mul`, `MeasureTheory/Integral/Layercake.lean:479` |
| Elementary ENNReal Markov | `mul_meas_ge_le_lintegral₀`, `MeasureTheory/Integral/Lebesgue/Markov.lean:50`; `meas_ge_le_lintegral_div` at104 |
| Lp Markov | `mul_meas_ge_le_pow_eLpNorm'`, `MeasureTheory/Function/LpSeminorm/ChebyshevMarkov.lean:45`; `meas_ge_le_mul_pow_eLpNorm_enorm` at52 |
| Norm as power integral | `eLpNorm_eq_lintegral_rpow_enorm_toReal`, `MeasureTheory/Function/LpSeminorm/Defs.lean:98`; `lintegral_rpow_enorm_eq_rpow_eLpNorm'` at131 |
| Indicator/restriction identity | `eLpNorm_indicator_eq_eLpNorm_restrict`, `MeasureTheory/Function/LpSeminorm/Indicator.lean:38`; indicator-constant formula at104 |
| Finite sums/Minkowski | `eLpNorm_sum_le`, `MeasureTheory/Function/LpSeminorm/TriangleInequality.lean:127`; useful but does not alone perform restricted interpolation |
| Monotone convergence | `lintegral_iSup`, `MeasureTheory/Integral/Lebesgue/Add.lean:34`; AEMeasurable variant at96 |
| Nonnegative sum integration | `lintegral_tsum`, `MeasureTheory/Integral/Lebesgue/Add.lean:360` |
| Tonelli swap | `lintegral_lintegral_swap`, `MeasureTheory/Measure/Prod.lean:1068` |
| Canonical simple approximation | `SimpleFunc.monotone_eapprox`, `SimpleFunc.iSup_eapprox_apply`, `SimpleFunc.iSup_coe_eapprox`, `MeasureTheory/Function/SimpleFunc.lean:895–910` |
| Finite power interval integral | `integral_rpow`, `Analysis/SpecialFunctions/Integrals/Basic.lean:147` |
| Convergent upper power tail | `integral_Ioi_rpow_of_lt`, `Analysis/SpecialFunctions/ImproperIntegrals.lean:172`; requires exponent<-1 and positive lower endpoint |

Some listed layer-cake formulas take real-valued f; extending/applying them to the ENNReal supremum requires truncation or a proved a.e.-finite representation. That is an explicit interface task, not already supplied by the current main maximal-shading theorem.

## Remaining geometric input, kept separate

The proved `MainMaximal` shading statements are not an existing operator definition. The direction-measure and operator modules still need to construct:

1. The actual normalized tube-average supremum and its equality to any countable measurable representative used in the proof.
2. All operator laws and output measurability for general functions, not just indicators.
3. The direction-cap measure estimate and finite selected-direction witness argument converting the literal shading theorem to (9.7), uniformly in all measurable E and positive level t.
4. Finite direction measure and the actual tube-volume lower bound yielding the strong-L1 coefficient.

Only after these are instantiated, and the two interpolation lemmas above are proved, can (9.8) be claimed as a new kernel-checked result. This plan introduces no custom operator axiom and changes no frozen theorem.
