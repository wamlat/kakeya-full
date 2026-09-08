# CapSelection: finite-arity rounding and finite direction-cell thinning

## Completed extension

`audit_work/formalization/CapSelection.lean` contains 20 theorem declarations and compiles cleanly with the existing Lean 4.33.1 / Mathlib 0df444a360eaa60ab8c11dca51a86af692955474 environment.

The earlier binary result is now extended by a **direct arbitrary-finite-arity construction**, rather than by assuming the binary encoding works. A `CapacityTree.node` carries any natural number of children indexed by `Fin arity`. Children must partition their support (pairwise disjoint supports). Leaves hold actual finite sets of original elements. Empty supports, zero capacities and zero-child nodes are allowed.

1. `attainsRank` constructs an actual finite subset attaining the recursively computed rank `min(parent capacity, sum child ranks)`. It recursively selects child subsets, takes their disjoint union, and truncates that union if the parent capacity binds. `admissible_mono` proves truncation preserves every descendant capacity.
2. `mass_le_rank` proves each feasible fractional mass is below that integer rank; `fractionalSelection` therefore rounds an arbitrary feasible weight vector in [0,1] to a genuine subset without losing its total mass.
3. `Occurs` identifies actual constrained blocks anywhere in the hierarchy. `all_capacities` turns recursive admissibility into the explicit inequality `card(selected ∩ block) ≤ capacity` for every such block.
4. `uniformSelection` retains at least rho times the original population whenever every block has at least that fractional capacity. `inverseCoefficientSelection` retains at least M/A for A≥1 if each original block population is at most A times its assigned integer capacity. The proof applies fractional rounding once; it does not lose an inverse coefficient at every tree level.
5. `terminal_unique` and `terminal_fibers_injective` prove that terminal fibers assigned capacity1 contain at most one selected original element. The fibers are actual finite preimages of a cell-label map, not an assumed injectivity condition in the final selection theorem.
6. `monochromaticSelection` constructs one finite color class retaining at least 1/(number of colors) of a selected set; all upper capacities survive. `inverseCoefficientColorSelection` composes this with the single M/A selection.
7. `latticeCellSelection` uses the explicit coordinatewise modulo3 coloring of integer lattice cells. It retains at least M/(A*3^dimension), respects all hierarchy capacities, and proves that every two distinct retained elements have some lattice coordinate differing by at least3. Terminal capacity1 handles distinct elements in the same cell; equal modular colors handle distinct nearby cells. No proper coloring is assumed: the modular coloring and its separation property are proved.
8. `covered_query_capacity` proves any finite query covered by hierarchy blocks has selected population at most the sum of those blocks' capacities. `covered_query_uniform_bound` specializes this to K covering blocks, each of capacity B, giving at most K*B. Covering blocks may overlap. This explicitly bridges tree constraints to external cap/query inequalities once a geometric covering is supplied.

## What is and is not closed

The finite-arity gap noted in the earlier binary module is closed directly. The finite selection, proportional retention, capacity-one terminal cells, color extraction and lattice-index separation are actual conclusions proved from finite data, without assuming an integral rounding result.

The remaining direction-space geometry is still substantive and is **not** claimed proved by this module:

- Construct a finite dyadic direction-chart hierarchy whose supports partition the relevant tube directions at every level.
- Check the precise integer capacities (including ceilings and terminal cells) against the manuscript's cap hypothesis uniformly in the coefficient and scales.
- Relate the finite original-cap coefficient A in this file to the coefficient and separation-scale factors at each intended application of the manuscript's thinning lemma.
- Prove the geometric covering count taking an arbitrary angular cap to boundedly many hierarchy cells of the suitable scale, then instantiate `covered_query_uniform_bound` with the desired scale-dependent capacities.
- Convert the proved separation of lattice cell indices to quantitative separation of actual projective directions under the chosen charts.

These are geometric embedding/covering obligations. They are not hidden premises asserting that the desired selected tube family already exists.

## Verification

From `/Users/ssoh/Documents/Codex/2026-09-06/work/audit_work/formalization`:

```sh
/Users/ssoh/.elan/bin/lake env lean CapSelection.lean
```

Final compile: exit0, no warnings or errors. No `sorry`, `admit`, `native_decide`, or custom axioms occur. For the kernel dependency audit, `audit_work/cap_selection_axioms.lean` contains the full source followed by `#print axioms` for all 20 theorems. Its stdout is recorded in `audit_work/cap_selection_axioms.log`.

The completed axiom audit reports all 20 declarations using only the standard foundational axioms `propext`, `Classical.choice`, and `Quot.sound`; no `sorryAx` or custom axioms occur.
