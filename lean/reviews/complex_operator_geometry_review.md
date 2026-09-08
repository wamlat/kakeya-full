# Separate statement review: complex-valued maximal operator

Read-only review of `formalization/ComplexOperator.lean`, SHA256 `173adb29079b8fa60f45022043df4978a4c468cf5fe07a928c44617d973db99a`. No source edits or new axioms; the parent owns compilation and dependency auditing.

No mathematical or statement-scope defect found. The input is an actual complex-valued function on Euclidean space, and the operator is exactly the existing supremum of normalized integrals of its scalar norm over the original unit tubes. `maximal_eq_norm` identifies this with the real-input operator applied to `x ↦ ‖f x‖`; it does not identify complex tube integrals with their absolute values.

`from_real` preserves the same epsilon, scale, sphere measure and positive constant. The constant is chosen before the function, scale and family of witnessing tubes. `AEMeasurable.norm` supplies the precise hypothesis of the real-input estimate, and `eLpNorm_norm` gives the actual complex input norm. Infinite input norms are allowed by the existing ENNReal inequality; no finite-integral or extra pointwise measurability assumption is introduced. Every endpoint wrapper invokes the corresponding proved real endpoint.

Thus the complex version of the usual absolute-average formulation of (9.8) is covered. The statement does not redefine the operator as a signed or complex average, for which a separate modulus convention would need to be specified.
