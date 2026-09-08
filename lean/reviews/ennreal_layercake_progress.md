# ENNReal power layer cake

`ENNRealLayerCake.lean` is frozen and clean-built. Its `power_layercake μ hf hp` proves the exact identity

`∫ f^p = ofReal(p) * ∫_{t>0} μ{x | ofReal(t)<f(x)} * ofReal(t^(p−1)) dt`

for every measurable ENNReal-valued f, every measure μ, and p>0. There is no finite-input, finite-output, a.e.-finite or SFinite hypothesis.

The proof constructs literal finite truncations min(f,n). Their real representatives satisfy Mathlib's proved real layer-cake theorem, since each truncation is finite and measurable. The truncations increase to f even at points where f=infinity. The positive-power map is a proved order isomorphism, so their powers increase to f^p. For every threshold, the strict level set of f is exactly the increasing union of the truncation level sets. Continuity from below of measure and monotone convergence on both sides then establish the identity. The level-measure function is measurable because it is antitone in the real threshold; no measurable-selection assumption appears.

This is a genuine extension of the pinned Mathlib real-valued theorem, used by both interpolation stages. It does not assert any operator estimate.

Verification: zero-diagnostic compile and exact full-source audit PASS for ten local declarations, including nine theorem declarations; seven named source theorems and one definition. Only propext, Classical.choice and Quot.sound occur. Evidence is in ENNRealLayerCakeSourceAudit.lean, ENNRealLayerCake_axioms.log and ENNRealLayerCake_audit.json.

Frozen SHA-256: `33f4b0cd579326772d22d39186b7881d16f1c58520c6657974eefa83721bb8e2`.
