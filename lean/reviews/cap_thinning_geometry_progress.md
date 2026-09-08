# CapThinningGeometry: global geometric cap-preserving thinning

`audit_work/formalization/CapThinningGeometry.lean` contains 41 theorem declarations. All compile using Lean 4.33.1 and Mathlib commit 0df444a360eaa60ab8c11dca51a86af692955474.

## Completed global theorem

Namespace `KakeyaFormal.CapThinningGeometry`, theorem `full_cap_thinning`.

Write ambient dimension d=k+1 and let F be an actual indexed unit-direction family. For any real m≥0, A≥1 and 0<delta≤r≤1 satisfying the actual predicate `F.CapBound delta m A`, the theorem constructs a finite set S of original tube indices such that

- `|S| ≥ M/[Cret(k,m) * A * (r/delta)^m]`;
- different selected indices have actual projective chord distance at least `2*r/d`;
- for every actual projective cap center and every r≤u≤1, its selected population is at most `Ccap(k,m)*(u/r)^m`.

The constants are explicit:

`Cret(k,m) = 2*d*packingConstant(k)*(d+1)^m*3^k`,

`Ccap(k,m) = 4*5^k*2^m*d^m`,

where `packingConstant(k) = 2*d*[4*d*(d+1)+5]^k` was independently proved in ProjectiveGeometry.

These constants depend only on dimension and m, never delta, r, A, M, tube locations or the directions. The A-loss is one inverse power. The new separation is a fixed positive dimension-dependent multiple of r. The statement does not assume original separation, m≤k, distinct directions, a selected hierarchy, block capacities, a desired rounding theorem, or a finite cap cover. Its cap centers need not be unit vectors, so this conclusion is stronger than the center restriction in the existing `TubeFamily.CapBound` predicate. The conclusion is phrased as original index cardinalities; reindexing this finite subset as a new TubeFamily is a separate bookkeeping interface.

## Genuine construction

1. Occupied images of arbitrary finite labels produce actual finite partitions and all descendant supports. The tree has arbitrary finite arity, and partitionedness is proved from fiber disjointness.
2. Every constrained occupied block at every depth is proved to occur. Uniform fractional weights yield feasible integer capacities `ceil(rho*original block population)`; applying the previously proved CapSelection rank construction gives actual selection and proportional retention.
3. Fine projected chart labels are actual integer floors. Dyadic ancestors are integer division by powers of two, including negative labels. Coherence and the exact identity with physical floors at side length h*2^j are proved.
4. The actual original m-cap condition bounds every dyadic chart block. Small blocks use the unit-sphere chart inverse distance bound and an existing direction as the cap center; blocks larger than radius one use CapCover's genuine finite projective cover. This gives B*2^(jm) population, with B=packingConstant*A*(chartConstant*h/delta)^m.
5. Proportional rounding with weight1/B selects at most one index per fine cell and at most ceil(2^(jm)) in each ancestor, retaining at least M/B.
6. Residue coloring modulo three retains a 3^(-k) fraction and all upper capacities. Different selected cells have an integer coordinate gap at least3, which implies a physical difference at least2h. A positive hemisphere coordinate at least c≥h also bounds the antipodal chord below2h, so this is actual projective separation.
7. Every projective cap of radius u is split into two ordinary caps centered at the two signs of its center. At a chosen dyadic scale u≤h*2^j≤2u, its labels lie in two explicitly constructed radius2 integer boxes, with at most2*5^k labels. Summing established block capacities gives the arbitrary-cap estimate. A finite dyadic depth reaching1 is constructed for every positive h; no infinite tree is invoked.
8. An actual signed-coordinate chart containing at least M/(2d) indices is selected using each unit vector's large coordinate. Signed coordinate maps are proved involutions and preserve actual cap bounds. Taking h=r/d ensures the needed positive-chart separation for every r≤1. Returning to the original directions preserves all counts and projective distances.

## Relation to manuscript and remaining scope

This closes the previously missing elementary finite laminar/geometric cap-preserving thinning step, with explicit harmless dimension/m constants and the correct fractional exponent m. It does not prove the analytic pivot, hairbrush, collision-shell, maximal estimate, or induction step. It does not assert that unrestricted spatial rescaling by itself yields the new direction separation; the subset must be selected using this theorem. Separate measurable/angular convention interfaces remain as stated in other reports.

## Reproducible verification

From `audit_work/formalization`:

```
/Users/ssoh/.elan/bin/lake env lean -o .lake/build/lib/lean/CapThinningGeometry.olean CapThinningGeometry.lean
/Users/ssoh/.elan/bin/lake env lean ../cap_thinning_geometry_axioms.lean > ../cap_thinning_geometry_axioms.log
```

The audit source appends `#print axioms` for every theorem in this exact source. Axiom results are checked for all41 declarations and permit only the standard Lean/Mathlib foundations `propext`, `Classical.choice`, `Quot.sound`. No `sorry`, `admit`, native_decide, custom axiom or unproved analytic input is introduced.
