# OriginalPivotSlabs: original marked input to simultaneous actual lift slabs

Status: complete and frozen. `OriginalPivotSlabs.lean` compiles to its `.olean` without warnings. Both local theorems were checked from their complete source bodies and print exactly `propext`, `Classical.choice`, `Quot.sound`. The three abbreviations and two proof-bearing record declarations were also inspected. No sorry, admit, custom axiom or unsafe declaration occurs. Compile and full-source theorem-axiom log: `original_pivot_slabs_compile.log`.

## Original inputs, fixed constants, and actual output

`Hypotheses` collects only original configuration requirements: positive small scale, original cap coefficient/density/marked fraction/count, admissibility, separation, boundedness, comparable full shadings, original marked inclusion/mass, fixed-theta 1/10 broad marks, full two-ends control, and the explicit logarithmic B and theta-inverse budgets. It contains no chosen angle, sample, pair, selected cell, output count, normalized ball bound or geometric smallness oracle.

`construct` first chooses a positive spatial-pruning constant K and a single positive delta0 <= 1 before the later original family, marks, delta,A,lambda,xi,B,theta. Fixed width is at least 1/12; alpha is fixed positive; the base DiscreteEstimate and its nonnegative m,d and p>=1 remain explicit. It invokes `UniformPrunedPivotSelection.construct`, then constructs the simultaneous actual `SelectedOutputSlabs.selectedLine` function from the returned selection and already derived geometry tests.

The returned `Package` keeps:

- the original pruning depth J and its scale-log bound;
- the exact threshold `cutoff K E delta A lambda xi m d p eps M J`, with per-scale loss (xi/100)/(J+1);
- the literal original `pruned` family O, tube equality, original shading inclusion, original comparison-union inclusion, deletion budget and small-radius spatial bound;
- the same `RecoveredInput`, with injective original index map, literal pruned full shadings and separate marked data;
- the actual dependent SampleSystem and Selection, preserving the original sigma bounds and Q lower bound;
- one actual `LineData` per unchanged original output index, including its chosen slab, exactly commonK cells, its selected original endpoint representative at each cell and all defining equalities;
- all original/normalized geometry Tests and explicit positive original scale and kappa in (0,1].

No count or incidence is reset in this packaging. In particular commonK is the selected pre-unit-normalization integer from the same actual dyadic fiber size. Subsequent genuine unit-segment normalization still incurs the proved factor three and must use actual cumulative incidence mass.

## Derived normalized spatial coefficient

Let n=k+2 be the original physical ambient dimension, Rnorm=1+2width and L the exact original pruning cutoff. The package proves, for every x and every r>=delta/Rnorm,

    # { z in recovered.family.unionCells :
          dist(cellCenter(delta/Rnorm,z),x) <= r }
      <= Cball * (r/(delta/Rnorm))^d,

with the exact coefficient

    Cball = PrunedGraphLift.spatialConstant(n,width,baseRadius,d) * L.

This follows from the original admissibility/boundedness, the actual small-radius bound on literal O, the recovered full-union subset of O, and the proved common-homothety transport. It does not presume that the original tubes remain admissible at the new mesh. Original integer labels are retained throughout.

`spatial_coefficient_ge_one` separately proves Cball>=1 from d>=0 and L>=1, by spatialConstant>=coverConstant(n,1)*2^d>=1. The Package exposes this as `normalized_coefficient_ge_one`, which is the exact input needed by the constructed grouped-pruning wrapper. It additionally exposes

    1 <= Cball * (16+2*(2width+n/2))^d

for the eventual graph cap coefficient. Neither displayed geometric coefficient contains an extra inverse power of kappa. L still retains its explicit original deletion-budget/density/scale dependence.

## Precise downstream use and remaining work

Consumers access `.recovered`, `.samples`, `.selection` and `.lines` directly. The selected graph families have original physical dimension n and lifted dimension n+1; the local `k` of SelectedOutputSlabs is therefore k+1 when the Package uses k.

The module closes original marked input -> actual selected slabs AND the normalized all-radius spatial premise. It does not itself normalize to unit tubes, construct colors, invoke the lifted DiscreteEstimate, perform high-cell incidence pruning or substitute the closing energy inequality. Those are the independently assigned `SelectedFamilyPruning` / `ConstructedPivotClosing` interfaces. The original logarithmic budgets remain assumptions to be produced by preceding reductions, and the final estimate at scales above delta0 still needs its separate coarse-scale branch.
