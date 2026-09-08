# Completed-measurable common localization

`LebesgueLocalization.lean` is clean-built and frozen at SHA-256 `714383c010dad54ecc9140b79f61f11486a9a6f215bf417f8a4d7c8c23cdb50e`. The unchanged-source environment audit passed all 16 local theorems and 34 local declarations; dependencies are only `Classical.choice`, `Quot.sound`, and `propext`. Its three named statements are `exists_selection`, `NullSelection.common_mass_lower`, and `NullSelection.density_depth_log_bound`.

This closes the completed-measurability clause of Lemma3.1 (combined.txt:393) at the common-radius/common-density selection interface. For an actual finite family of original completed-measurable sets in unit balls, with positive common lower mass and finite upper mass, it constructs both common dyadic classes and actual original selected indices. It retains the same radius/depth bounds, radius-to-alpha original mass fraction, density interval, two class-count loss and all-radius two ends as the proved Borel construction.

The returned sets are literally `Y i ∩ closedBall (centers i) rho` for the original Y. Their certified measurability is correctly `NullMeasurableSet`; the theorem does not claim these original intersections are Borel. It first constructs measurable subset representatives, applies actual `CommonDensityLocalization.exists_selection`, then transfers all original/ball/intersection measures exactly using a.e. equality. The witness choice is internal, and no desired selection, count, measure inequality or two-ends conclusion is assumed. The ambient measure is arbitrary; finiteness is required only for original individual rows, exactly as in the original Borel API.

All frozen406 sources and registries remain unchanged. This module is a verified addition outside that snapshot.
