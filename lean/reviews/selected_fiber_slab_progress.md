# Actual slab selection and common integer density

`formalization/SelectedFiberSlab.lean` adds six proved theorems and one definition after the 11-theorem `SelectedFiberLift` population module. This completes the optional finite slab/trimming step of combined §5.5, using actual populated cells rather than supplied cell counts.

Assume an actual nonempty finite set `S` of normalized legal `LabeledPair` samples, one legal reference pair, and the same actual centered pivot label for every member of `S` and the reference. Besides `0<delta≤1` and `0<kappa≤1`, the time-range/slab result explicitly requires `k delta≤kappa^5/4`. This is the scalar room needed after the already proved actual pivot-coefficient rounding error `k delta`; it is not hidden in an asymptotic notation.

`lift_time_bounds` derives `1+kappa/2 ≤ c/u_reference ≤ 2/kappa` from that actual rounding. Centered grid rounding then puts every occupied lifted cell's center height in `[0,3/kappa]`. `unit_slab_selection` constructs the finite classification by the natural floor of this center height; at most `ceil(3/kappa)+1 ≤ 5/kappa` classes occur. It chooses one actual unit slab, preserving at least `kappa/5` of the distinct lifted cells.

With `C=multiplicityConstant(k,width)` from `SelectedFiberLift`, `populated_slab` consequently constructs a nonempty actual cell set in one unit slab with cardinality at least `kappa^5 #S/(5C)`.

The common integer is defined exactly as

`K = max(1, floor(kappa^6 #S/(10C)))`.

`common_integer_slab` proves that the chosen slab contains at least `K` cells and constructs an actual subset `V0` of exactly `K` cells. It proves `K≥1`, `K≥kappa^6 #S/(20C)`, and `K≤kappa^6 #S/(10C)+1`. It also constructs an injective representative function from retained cells to original samples in `S`, with each representative rounding to that very cell. There is no division by the number of incident angles or assumption that the unrounded density exceeds one.

If all selected angle-output sample fibers have the same cardinality `h`, this definition gives precisely the same integer `K` for all of them. The slab and reference may vary; neither enters `commonCount`.

`common_density_upper` additionally derives

`delta K ≤ 1+fiberConstant(k,width)/(10C)`

from the actual geometric original pivot-fiber bound in `PivotOutputCount`. Thus the upper density constant is uniform, rather than assumed. Combined with the lower bound, this gives the explicit finite form of the density bounds around (5.22).

Remaining downstream work is to assemble these per-output chosen fibers/slabs over all outputs and groups and translate each selected unit slab into the normalized graph input. For arbitrary real delta, a translation by an integer slab height should be implemented using a grid-compatible vertical shift (with its one-mesh boundary error), or justified by the dyadic reciprocal-integer scale condition. This module proves actual pre-translation center heights and does not silently identify a non-grid translation with an integer relabeling.

Both modules compile and build their `.olean` files without warnings. The five main slab theorem axiom checks use only `propext`, `Classical.choice` and `Quot.sound`; no `sorry`, `admit` or custom axiom is present. Compiler logs: `audit_work/selected_fiber_lift_compile.log` and `audit_work/selected_fiber_slab_compile.log`.
