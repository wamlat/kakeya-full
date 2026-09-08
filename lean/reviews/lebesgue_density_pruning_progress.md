# Completed-measure density pruning on the original sets

New source: `LebesgueDensityPruning.lean`, SHA-256 `bb2474418b4adc435bc08e504ecd982ac2221b5a804e05bc7f7a004cb6e93010`. The source is clean-built and frozen outside the original checkpoint-22 set of 406 modules. Existing files and registries were not changed.

The module closes the completed-measurable scope of the actual §3.3 pruning construction. Mathlib's `NullMeasurableSpace X mu` makes the original null-measurable sets measurable, and `mu.completion` has exactly the same outer measure on every set. The named `mass_completion`, `survivors_completion`, and `retained_completion` identities are proved by reflexivity. Thus these wrappers retain the very same original full and assigned shadings, density thresholds, surviving masks, half-multiplicity good sets, pieces and retained group labels.

`good_nullMeasurable`, `goodRows_nullMeasurable`, `badRows_nullMeasurable` and `pieces_nullMeasurable` prove completed measurability of the actual output sets. `bad_mass_le_deleted`, `mass_split` and `good_mass_lower` instantiate the original integral proofs with the completed measure and express their conclusions using the original measure. They keep the exact finite-measure assumption needed for subtraction of real incidence masses.

The public `source_fractions` takes only the original null-measurability and finite row masses, nonnegative kappa, original one-group assignment, and actual total mass premise. It constructs the original deletion threshold `kappa/8` and proves exactly:

- deleted assigned mass is at most one eighth of the original assigned mass;
- good surviving mass summed over all pieces is at least three quarters;
- retained good mass is at least five eighths.

These are the same numerical fractions and actual sets as `SourceDensityPruning.source_fractions`. Empty families, zero mass and empty pieces remain allowed. No selection, retention, integration or geometric conclusion is supplied as a premise.

The existing `SourceDensityPruningGeometry.active_density`, `all_rows_two_ends`, `marked_piece_broad`, `retained_overlap` and `retained_marked_overlap` impose no `MeasurableSet` hypothesis on the original shadings. They already apply directly under the original measure to these unchanged masks. Hence the completed-measure instantiation retains the original surviving-row density bounds, exactly the `1/a` full-two-ends loss, exactly factor-two marked broadness, and unchanged pointwise overlap comparison. There is no need to change the ambient Euclidean geometry to the completion's type alias or weaken those conclusions to almost-everywhere statements.

Validation uses Lean 4.33.1 with pinned mathlib `0df444a360eaa60ab8c11dca51a86af692955474`:

```
lake env lean -o .lake/build/lib/lean/LebesgueDensityPruning.olean LebesgueDensityPruning.lean
python3 ../audit_lebesgue_density_pruning.py
```

The compiler returned zero diagnostics. The exact-source audit passed all eleven named theorems, eleven local theorem declarations and eleven total local declarations, with only standard axioms (`propext`, `Classical.choice`, `Quot.sound`). Evidence is recorded in `lebesgue_density_pruning_audit.json` and `LebesgueDensityPruning_SourceAudit.log`; the parent owns subsequent integrated verification. The parent independently reviewed all eleven statements and proofs at these bytes and reported no defect. This is a measure-completion instantiation of already proved actual constructions, with no custom axiom or new analytic input.
