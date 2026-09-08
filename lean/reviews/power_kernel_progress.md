# Exact interpolation power integrals

PowerKernel.lean is frozen/clean-built and exact-source audited PASS: 3 named theorems, standard foundations only. It proves the actual ENNReal integral of t^s on (0,U), s>−1,U>0, and derives the scaled kernel integral of (t/U)^(-b)t^(r−1) as U^r/(r−b), b<r. These identities use Mathlib's proved real interval integral and the nonnegative integral conversion; no integral evaluation is assumed. The shared kernel is consumed by both first and second interpolation stages. This small module itself makes no operator-norm claim.

Audit metadata: power_kernel_audit.json; exact-source audit power_kernel_axioms.lean/log. Reproduce with lake env lean PowerKernel.lean and lake env lean ../power_kernel_axioms.lean.
