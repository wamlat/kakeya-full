# Angle/output fiber selection: completed bounded phase

`formalization/AngleFiberSelection.lean` formalizes the finite selection logic of combined PDF §§5.3–5.4 (source text lines 1004–1120). It contains 14 proved lemmas/theorems and 9 actual finite definitions. The main theorem is `KakeyaFormal.AngleFiberSelection.select_angle_fibers`.

## Inputs and exact losses

The data are an actual nonempty finite angle set `A`, an actual finite legal-sample set `P a` for every angle, an angle-specific output map `out a`, and a second-tube label `label a`. The original fiber is defined literally by filtering `P a` for output `f`; the edge set consists of pairs `(a,f)` with a nonempty such fiber.

Geometric inputs remain explicit:

- `mu > 0` samples per angle: `mu ≤ #(P a)`;
- at most `U` actual outputs per angle;
- low-fiber threshold `t ≥ 0`, calibrated by `t U ≤ mu/2`;
- integer upper bound `B` for every original fiber;
- positive integer `K` bounding the number of distinct second-tube labels at each output (a local bound, not a bound on the global set of tubes).

Put `J = Nat.log 2 B + 1`. The theorem constructs one integer `j < J`, `h = 2^j`, and the actual whole-edge set

`Omega = {e in original edges : t ≤ #fiber(e), h ≤ #fiber(e) < 2h}`.

Both `Omega` and the subsequent `OmegaStar` are proved nonempty. The exact bounds are

- `1 ≤ h ≤ B` and `t/2 < h`;
- selected sample mass `Σ_{e in Omega} #fiber(e) ≥ mu·#A/(2J)`;
- `#Omega ≥ mu·#A/(4hJ)`;
- `#Omega ≤ K·#OmegaStar`, hence `#OmegaStar ≥ mu·#A/(4hJK)`.

The first factor 2 is actual low-fiber deletion; `J` is actual dyadic pigeonholing; the second factor 2 comes from dividing by the upper endpoint `2h`. Taking `sigma=h/N` gives `sigma > t/(2N)` and `sigma ≤ B/N`. With the paper's `mu ~ lambda^3 N^3`, `t ~ lambda^2 N`, and `B ~ kappa^(-1)N`, these are precisely the constant-factor content of (5.14), with no assumption that `lambda^2 N` exceeds one.

## Most-frequent label selection

`frequent_class` chooses a genuine maximum-cardinality label class from each actual output fiber of edges. `frequent_output_labels` takes the disjoint union of these choices. It proves:

- `OmegaStar` is a subset of `Omega`;
- its actual output support equals the original support of `Omega`;
- all retained edges at one output have the same second-tube label;
- every edge in `Omega` with that output and chosen label is retained;
- the retained local degree is at least the degree of every alternative second-tube class.

This is whole-edge selection. No sample fiber is shortened or replaced at this stage. Substituting the geometric local-label estimate `K ~ kappa^(-2(k-1))` yields (5.16).

## Actual collisions and support

`collisionPairs OmegaStar` is the actual finite set of ordered pairs of retained edges with equal outputs, including diagonal pairs. `collision_energy_count` proves that its cardinality equals

`collisionEnergy OmegaStar = Σ_f #(outputEdges OmegaStar f)^2`.

`collision_cauchy` proves `#OmegaStar^2 ≤ #support·collisionEnergy`. The main theorem consequently returns, for every positive real `E` satisfying the geometric upper bound on this actual energy,

`[mu·#A/(4hJK)]^2 / E ≤ #support`.

Substituting `E ~ kappa^(-(k-1)) N^2 L #A`, `J ~ L`, `h=sigma N`, and the preceding `mu,K` gives the exact exponent/count pattern of (5.19): `kappa^(5(k-1)) lambda^6 sigma^(-2) N^2 #A L^(-3)`. The instantiated kappa monomial algebra is not a separate theorem in this module; the stronger explicit finite formula is the formal output. No geometric collision upper bound or support conclusion is silently assumed.

## One actual angle per output

`exact_fiber_representatives` injectively indexes the distinct retained outputs by `Fin Q`, with image equal to the actual support. It chooses one incident angle `a(i)` for each output and an actual subset `R(i)` of `fiber P out a(i) f(i)` of exactly `h` samples. It proves the exact mass identity `Σ_i #(R(i)) = hQ`.

Thus each selected sample set belongs to one original angle and one output. It is never a union over angles. There is no loss involving the output's angle multiplicity. The construction uses Lean's fixed classical choices and is an existence proof, not an executable ordering algorithm.

## Remaining geometric/analytic interfaces

This closes the finite selection logic through the inputs to §5.5. It does not prove geometric legal-sample abundance, the output/fiber upper bounds, the projective local second-tube packing count, or the geometric collision upper bound. The natural-log/scale estimate turning `J = log_2 B+1` into `O(log N)` still uses the geometric scale relation controlling `B`; no such relation is assumed implicitly.

The output consists of original samples. Passing to `LiftedAnalytic` still requires the actual sample-to-lifted-cell map, its bounded multiplicity, the fullest-slab choice and common integer cell trimming of (5.20)–(5.23), followed by the actual graph incidence and pivot residual witnesses. In particular, `hQ` sample mass is not identified with lifted-cell incidence mass without that multiplicity/slab step. Distinct output labels are already injectively indexed, supporting the later fixed-pivot restriction.

## Verification

Compilation passes with Lean 4.33.1 and the pinned mathlib; the `.olean` is built. There are no warnings, `sorry`, `admit` or custom axioms. Seven principal theorems, including the assembled selection, are axiom-audited and depend only on `propext`, `Classical.choice` and `Quot.sound`. Final compiler output: `audit_work/angle_fiber_compile.log`.
