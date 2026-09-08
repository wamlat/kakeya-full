# Geometry needed for the maximal-operator implication in Section 9.3

This is a read-only dependency plan against the pinned Mathlib revision `0df444a360eaa60ab8c11dca51a86af692955474` and the frozen project sources. It addresses (9.7), extracted manuscript lines 1876–1888; interpolation to (9.8) is outside this task. No operator theorem is claimed proved by this report, and no source or axiom was added.

## Concrete operator and direction measure

Use the actual Euclidean sphere `Direction n := Metric.sphere (0 : Space n) 1` with its usual subtype topology. Its direction measure should be

`sphereMeasure n := (volume : Measure (Space n)).toSphere`.

Mathlib's `Measure.toSphere` is the canonical polar-coordinate sphere measure: `toSphere_apply'` expresses a measurable cap's measure as `n` times the ambient volume of its radial cone. The file also supplies the finite-measure instance and `toSphere_real_apply_univ`. These are in `Mathlib/MeasureTheory/Constructions/HaarToSphere.lean` (definition near line 52, cone formula near 71, total measure near 101, finite-measure instance near 120). Restricting ambient Lebesgue measure to the sphere would be wrong: that gives the zero measure in the positive dimensions of interest.

For a direction `v` and base `b`, use the literal `UnitTube` with base `b` and direction `v.val`. For indicators define

`density(delta,E,b,v) = volume.real(E ∩ tube(b,v).carrier delta) / volume.real(tube(b,v).carrier delta)`.

At positive delta the denominator is finite and positive by `TubeVolume.carrier_finite` and `carrier_volume_lower`, and this density belongs to `[0,1]`. Define the restricted operator as the real supremum over all bases. The range is nonempty and bounded above by one, so `lt_csSup_iff` gives an actual strict witnessing base whenever `lambda < supremum`; no maximizing tube or measurable selection is required. Verified API: `Mathlib/Order/ConditionallyCompleteLattice/Basic.lean:366`. Alternatively use an ENNReal indexed supremum, with `lt_iSup_iff` from `Order/CompleteLattice/Defs.lean:314`.

The source treats directions as unoriented. A small new reversal lemma should identify the carrier of `(base=b,direction=v)` with that of `(base=b+v,direction=−v)`, using the parameter change `t ↦ 1−t`. Thus a supremum using the oriented representative `v` still ranges over precisely the source's unoriented tubes, and the operator is antipodally symmetric. There is no need to construct a projective quotient or change the sphere's metric/measure instance.

## Finite covers with witnesses in the actual level set

There is a short route using existing APIs that avoids building a new maximal-net theorem on a projective pseudometric space.

1. Any subset `S` of the direction sphere is totally bounded, whether or not `S` has yet been shown measurable. Use `(isCompact_sphere 0 1).totallyBounded.subset` and `Metric.exists_finite_isCover_of_totallyBounded` at Euclidean radius `delta/4`. The latter gives a finite net **contained in S**, not centers outside the level set. Verified sources: `Topology/MetricSpace/ProperSpace.lean:47` and `Topology/MetricSpace/Cover.lean:106`. Its radius is `NNReal` and its conclusion uses `edist`, requiring only elementary real-radius conversion.
2. Convert that finite set to a `Finset` and apply the project's `CapCover.finite_projective_net` at projective radius `delta/2`. Every retained center still belongs to `S`; directions are projectively `delta/2`-separated. `ProjectiveGeometry.projective_le_chord` and `projective_triangle` show that every original level-set direction is within projective distance less than `delta` of a retained center (`delta/4 + delta/2 < delta`).
3. At each of these finitely many actual level directions, choose its strict witnessing base. Reindex the finite net injectively by `Fin M`. This constructs a literal `TubeFamily` and actual shadings `E ∩ tube_i.carrier delta`. Apply `MaximalShading.Estimate` with the fixed separation coefficient `1/2`.

This resolves the direction-cover/witness dependence: one must not start with an arbitrary sphere net and assume its centers inherit the level-set witnesses. The construction above retains centers in the actual level set throughout. Empty level sets and empty finite families can be handled directly.

## Sphere-cap upper bound from already proved tube volume

The needed bound is an **upper** bound `sphereMeasure(cap(v,r)) ≤ C_n r^(n−1)`. The library's `toSphereBallBound_mul_measure_unitBall_le_toSphere_ball` is a **lower** bound and cannot supply this step. The project's finite projective packing theorems likewise bound cardinalities, not spherical measure.

A direct new geometric proof uses the cone formula. If `u` is a unit vector with `norm(u−v)<r` and `0<t<1`, then

`dist(t*u, t*v) = t*norm(u−v) ≤ r`.

Hence the radial cone over this chord cap lies in the actual radius-r tube with base zero and direction v. For `0<r≤1`, `TubeVolume.carrier_volume_upper` gives cone volume at most `U_n*r^n/r`, where `U_n = 3*2^n*unitBallVolume(n)`. Applying `Measure.toSphere_apply'` yields the oriented-cap estimate `n*U_n*r^(n−1)`. A projective cap is contained in the union of the chord caps centered at v and −v, so the fixed constant can be `2*n*U_n` for `n≥1`.

The cap sets are Borel because the projective distance is the minimum of two continuous norms; this continuity lemma is elementary but has not yet been added to the project. Finite subadditivity then bounds a covered level set by `C_n*delta^(n−1)*M`. This bound remains valid as an outer-measure statement even before level-set measurability is established. Relevant checked APIs: `MeasureTheory.measureReal_mono`, `measureReal_iUnion_fintype_le`, and `measureReal_biUnion_finset_le` in `MeasureTheory/Measure/Real.lean`; all direction sets have finite measure under `toSphere`.

## Restricted weak estimate and exact exponents

The actual witness family has shading density at least lambda. The proved `MaximalShading.Estimate n a` therefore gives

`volume(E) ≥ c*delta^(n−a+eps)*lambda^a*sum_i volume(tube_i)`.

Use the actual tube lower bound `volume(tube_i) ≥ l_n*delta^(n−1)` from `TubeVolume.carrier_volume_lower`. Combining it with the direction-cap cover gives

`sphereMeasure{v : K_delta 1_E(v)>lambda} ≤ C*delta^(−(n−a)−eps)*lambda^(−a)*volume(E)`.

The estimate constant and the separation coefficient are fixed before delta, lambda, E, the net, or the witnessing tubes. No interpolation, extra scale loss, cap-count hypothesis, or desired operator estimate is needed here. For lambda≥1 the indicator level set is empty. For the first real-valued statement explicitly require `volume(E)≠infinity`; otherwise `volume.real E` becomes zero and is unsuitable. A final ENNReal version can include arbitrary measurable E by making the infinite-volume case trivial. Every finite witness union is finite because it is contained in a finite union of actual carriers.

## Measurability is a separate concrete obligation

An uncountable supremum of measurable functions is not automatically measurable. The finite witness argument does not itself close this point. Two usable routes are available:

- **Recommended:** prove continuity of the tube average in its direction for each fixed base, then use lower semicontinuity of the supremum over bases. A quantitative segment perturbation estimate is
  `abs(infDist(x,segment[b,b+v])−infDist(x,segment[c,c+w])) ≤ norm(b−c)+norm(v−w)`.
  The compact-segment parametrization by the same `t∈[0,1]` proves the associated Hausdorff bound. Existing APIs include `Metric.hausdorffDist_le_of_mem_dist` and `Metric.infDist_le_infDist_add_hausdorffDist` in `Topology/MetricSpace/HausdorffDistance.lean:842,890`. New glue is needed to identify the existing carrier with the closed delta-neighborhood of the segment and to prove indicator stability off its boundary.
- The carrier is a convex compact capsule (segment plus closed ball), so `Convex.addHaar_frontier` in `Analysis/Convex/Measure.lean:35` gives boundary measure zero once its convexity is supplied. The existing `TubeVolume.carrier_compact` already displays the required parametrization. Dominated convergence then proves continuity of numerator and denominator. For finite-measure E the numerator is bounded by `1_E`; alternatively work locally in a fixed compact ball. Verified APIs are `MeasureTheory.continuousAt_of_dominated` in `Integral/Bochner/Basic.lean:426` and `tendsto_integral_filter_of_dominated_convergence` in `Integral/DominatedConvergence.lean:67`.
- Finally apply `lowerSemicontinuous_ciSup` (real bounded suprema) or `lowerSemicontinuous_iSup` (complete-lattice values) in `Topology/Semicontinuity/Basic.lean:682,686`, followed by `LowerSemicontinuous.measurable` in `MeasureTheory/Constructions/BorelSpace/Order.lean:685`. Strict level sets are open by `lowerSemicontinuous_iff_isOpen_preimage` in `Semicontinuity/Basic.lean:175`.

A countable-base-supremum route is possible after translation continuity: `Dense.ciSup` in `Topology/Order/IsLUB.lean:194` reduces to a countable dense set of bases, while `Measurable.lintegral_prod_right'` in `MeasureTheory/Measure/Prod.lean:123` supports parameterized averages. This still requires actual continuity or a proved supremum-equivalence argument. The generic convolution-continuity theorem inspected in `Analysis/Convolution.lean:612` assumes a continuous kernel; it does not directly apply to the discontinuous tube indicator.

## Concrete next statement

Implement first a new `finite_indicator_witness_cover` theorem. Define the level set literally by existence of a base with tube-density greater than lambda, and prove from `0<delta≤1` and measurable finite-volume E that there exist a finite actual tube family and its actual intersections with E such that:

1. directions are projectively `delta/2`-separated;
2. every selected tube satisfies the strict density witness;
3. every direction in the full existential level set belongs to a projective radius-delta cap around one selected direction;
4. all selected shadings are measurable, lie in their respective literal carriers, and their union lies in E.

This statement requires no selected-count or cap-cover premise and constructs its witnesses using the two existing finite-net APIs. Next prove the cone-based `projective_cap_measure_upper`, then compose the proved maximal-shading estimate into the restricted weak outer-measure bound. Complete the tube-average continuity/supremum-measurability module before presenting that bound as the full measurable operator input for interpolation. The existing frozen project does not yet contain these operator definitions or new lemmas.
