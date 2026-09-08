# Measurable seed logarithmic prefactor

MeasurableSeedLogLoss supplies the uniform logarithmic and exact square-root-cap bound for an actual measurable angular construction. It is independent of the atom index set and does not assume whole-cell shadings.

The only variable geometric bookkeeping inputs are the actual depth J, its logarithmic upper bound, and delta<=tau<=1. The rate and eta budgets have the same fixed dimension-only numerators as the weighted angular selection. The exact densityConstant uses the ORIGINAL physical two-ends coefficient B, not an artificial grid-width enlargement. Its uniformConstant uses fixed B0; no dependence on A,delta,tau,J,lambda or population remains.

uniform_prefactor proves c/sqrt(A)*seedLog(delta)^(-uniformLoss) <= depthConstant*3retentionRate/16 /hairbrushLog(delta/tau)^(5/2). It keeps the exact cap factorization, bounds the inverse depth in the correct direction, and combines the additional inverse logarithm by an exact real-power identity. It does not by itself assert the measurable union theorem; that is the subsequent MeasurableSeedEstimate assembly.

Validation: clean production compilation, exact-production-source audit with all local declarations and source theorem coverage; only standard Lean foundations. Finite agent independently read/recompiled/reviewed and found no defect; see measurable_seed_log_loss_independent_review.md.

SHA256 `8b69548d93d9ba766989bb7cff6f855364d69efc44377f2f94a781316b1d0670`; 10 audited theorem declarations, 12 all local declarations; PASS.
