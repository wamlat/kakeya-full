# Exact original-set density trimming

`LebesgueDensityTrimming.lean` compiles without diagnostics at SHA-256 `79a5d42d97ea6c9f67fe2a311f6cc04e39ba42e8d49bfccadea80ee047fd68c0`. The exact-source audit passes both local theorem declarations and both total declarations, using only `Classical.choice`, `Quot.sound`, and `propext`.

The file explicitly exports the shrinking step in combined Section8.1 for arbitrary original Lebesgue-measurable shadings. `exists_exact_subset` first constructs an actual Borel subset of the original bounded input with equal volume, then applies the proved continuous radial-cut selection theorem. It returns a Borel subset of the original set with exactly any requested mass between zero and its mass, including both endpoints. The ambient dimension is positive, as required for the nonatomic volume argument.

`construct` performs this selection simultaneously for the original finite tube family and returns the existing `MeasurableDensityTrimming.Output F Y radius a` with the original Y. Thus its already-proved union containment, union-volume bound, total mass identity and inherited two-ends bounds apply without changing inputs. It does not use an exact-mass selection oracle or assume the output exists. This direct original-set consumer is outside the initial418-module freeze and will be included in the final additive extension.
