# Actual global angular groups and measurable realization

The following development modules are compiled with Lean 4.33.1 and the configured mathlib dependency. They construct the finite groups from `AngularAssignment.actual_angular_shading_assignment`; they do not assume the group selection, desired cap witnesses, or a desired measurable rounding estimate.

* `AngularGroupRestriction.lean`: 19 theorems. Restrict each group to precisely its nonempty original tube indices. This is actual finite reindexing, preserves mass and pointwise incidences exactly, inherits separation and cap bounds, and makes every remaining index satisfy the group's direction localization. Unique assignment gives disjoint active index sets and total active count at most the original tube count.
* `AngularGroupPruning.lean`: 7 theorems. Construct the retained group set by an actual incidence threshold. With initial retained fraction `rate` and original upper shading size `2 lambda/delta`, keeping groups above `(rate/4)(lambda/delta)` per active tube leaves mass at least `(3 rate/4)(lambda/delta) M` and summed active count at least `(3 rate/8) M`.
* `AngularSeedPieces.lean`: 11 theorems. The actual assignment gives a common scale `delta <= tau <= 1`, finite depth `J <= log(1/delta)/log 2`, fixed angular radius `3 tau`, rate `3/[8 C_k(J+1)]`, broadness coefficient `4^beta (4 C_k)`, and group overlap at most `2 tau^(-beta)`. Here `C_k = packingConstant(k) 3^k`. Pruning and exact index compression preserve the overlap.
* `AngularSeedRealization.lean`: 17 theorems. For every group, realize its actual cells and the corresponding full original shadings under one shared homothety with `W=max(1,width+ambient/2)`. The resulting unit tubes have physical width delta; directions, delta separation, and cap condition are unchanged. Full upper mass is `2(lambda/W^ambient) delta^(ambient-1)`. Each retained reference group has total mass at least `eta(lambda/W^ambient)delta^(ambient-1)` times its true tube count. Broadness remains pointwise, including boundaries. Original full shadings supply two ends with coefficient `B(1+ambient/2)^alpha W^alpha`. All reference group unions lie in the same transformed original union.
* `AngularSeedSummation.lean`: 8 theorems. Integrating the actual pointwise overlap gives the group volume sum bound `2 tau^(-beta) delta^ambient originalUnionCard / W^ambient`. The real-power identity needed to absorb this overlap into the hairbrush angular gain is proved for `beta <= (m-1)/2`.

Axiom audits compile full module sources with `#print axioms` on every theorem. Restriction, Pruning, Pieces, and Realization audits have completed and use only `propext`, `Classical.choice`, and `Quot.sound`; Summation has also completed its full-source audit with exactly these standard foundations. No `sorry`, custom axioms, desired rounding premise, or null-set boundary exception is introduced.

Commands run in `audit_work/formalization`:

```
/Users/ssoh/.elan/bin/lake env lean -o .lake/build/lib/lean/AngularGroupRestriction.olean AngularGroupRestriction.lean
/Users/ssoh/.elan/bin/lake env lean -o .lake/build/lib/lean/AngularGroupPruning.olean AngularGroupPruning.lean
/Users/ssoh/.elan/bin/lake env lean -o .lake/build/lib/lean/AngularSeedPieces.olean AngularSeedPieces.lean
/Users/ssoh/.elan/bin/lake env lean -o .lake/build/lib/lean/AngularSeedRealization.olean AngularSeedRealization.lean
/Users/ssoh/.elan/bin/lake env lean -o .lake/build/lib/lean/AngularSeedSummation.olean AngularSeedSummation.lean
```

Full-source audit files/logs: `audit_work/angular_{group_restriction,group_pruning,seed_pieces,seed_realization,seed_summation}_axioms.{lean,log}`.

Remaining at this checkpoint: directly apply and sum the new constructed measurable box hairbrush theorem; convert finite depth and the explicit eta losses into uniform logarithmic losses; absorb logarithms and connect to the final seed statement. The modules above alone do not claim that completed endpoint or recursive improvement.

## Direct finite seed checkpoint

`AngularSeedHairbrush.lean` (5 theorems) and `AngularSeedBound.lean` (2 theorems) now compile with full-source standard-foundation axiom audits. Every retained actual group is fed directly into `AngularBoxAlgebra.single_box_quadratic_density`, with no assumed group-volume estimate. Summing and cancelling the overlap gives:

`[seedConstant(k,J,width,alpha,beta,B,m,A) * 3 rate(k+1,J)/16 / W^(k+2)] * lambda^2 * M * delta^(k+1) * delta^((m-1)/2) / hairbrushLog(k,delta/tau)^(5/2) <= delta^(k+2) * originalUnionCard`.

Premises: actual family in ambient `k+2`, `0<delta<=tau<=1`, `0<lambda<=1`, positive alpha and beta, `beta <= (m-1)/2`, `m>=1`, `A,B>=1`, actual width-delta admissibility, comparable original density, delta-separated directions, actual cap condition, and original finite full-shading two-ends tests for every center and `delta<=r<=1`. The angular pieces `P` are constructible by `exists_pieces` from every positive original tube count and `0<delta<=1`; all their mass/locality/overlap properties are proved.

This checkpoint is a genuine finite two-ends seed inequality, with its depth and logarithmic losses visible. It is not yet a uniform epsilon-loss theorem, and does not remove the original two-ends assumption. The positive-beta condition requires `m>1`; the `m=1` endpoint requires a separate branch. Next development makes constants uniform in selected depth and scales, extracts the requested cap factor `A^-1`, and allows the original two-ends coefficient to grow by a prescribed logarithmic power.
