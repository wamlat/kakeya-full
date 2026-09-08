# Section 7 low-cell logarithmic absorption

`LowCellAbsorption.lean` is clean-built and stable. It contains eight theorems. The full source, followed by the production all-local-declaration audit command, compiled without diagnostics. All 15 resulting local environment entries depend only on `propext`, `Classical.choice`, and `Quot.sound`; no custom axiom is used.

Source SHA-256: `2b2ca55ea8d1be69659ed256e2df823b5d7364d0d7cc6122fd48e5530c2672bc`.

## Uniform low branch

`uniform_low_bound` fixes `cLow>0`, `xi₀>0`, `x≥0`, `C≥1`, `D<m+1`, and `eps≥0`. It then chooses `c>0` **before** every `δ, λ, ξ, M, E`. For

* `0<δ≤1`, `0<λ≤1`, `M≥0`;
* `ξ≥xi₀ log(2/δ)^(-x)`;
* `cLow ξ λ M/[δ log(2/δ)]≤E`,

it proves

`c δ^(m−D+eps) λ^C M≤E`.

All exponents and scalar parameters are real. The population can later be a cast natural cardinality; the statement includes zero populations. The proof uses the fixed margin `m+1−D+eps>0` to absorb the logarithmic power `x+1`, through the already proved `PivotLossAbsorption.inverse_log_delta`. It then uses `λ^C≤λ`. Consequently this deterministic branch does not require `λ≥δ^(1/3)` and permits zero final scale loss.

`uniform_low_cap_bound` has the same quantifier order and adds `A≥1`, obtaining the conventional extra factor `A⁻¹` by a proved monotonicity step. It is ready to combine with the actual sampled pivot branch using the minimum of the two fixed constants.

`threshold_low_identity R H xi lam M δ L` proves the exact identity

`((1/R)*(xi*lam*M/δ))/(2*(H*L)) = (1/(2*R*H))*xi*lam*M/(δ*L)`.

With `R=ratio c0 C0`, `H=highCoefficient (k+1)` and `L=log(2/δ)`, it matches the literal low alternative returned by `SamplingMeasurablePivot.low_or_pivot`. The identity itself is valid even at zero scalar values; its applications prove the necessary positive constants separately.

## Source-log transport

`log_eccentricity_transport` proves

`N^(1/a)≤N′, a≥1, N,N′>0 ⇒ log(2N)≤a log(2N′)`.

Taking `a=2k` gives the logarithmic comparison in the complement of Section 7's first coarse case. The additive `log 2` is included, so this is directly compatible with the formal loss budgets.

The mesh versions are `log_scale_transport` from `δ′^a≤δ`, and `log_scale_transport_of_power_cutoff` from `δ′≤δ^(1/a)`. Both conclude `log(2/δ)≤a log(2/δ′)`.

`inverse_log_scale_transport` converts an original-mesh marked budget to

`ξ≥(xi₀ a^(-x)) log(2/δ′)^(-x)`

when both meshes lie in `(0,1]`. `uniform_original_log_low_bound` combines this transport and the actual normalized low inequality into the target at `δ′`, with a fixed positive constant chosen before both meshes and the configuration parameters.

## Exact remaining boundary

The module does not assume the desired pivot conclusion or a random-outcome existence theorem. It consumes the actual deterministic low-support lower inequality, which is supplied separately by the finite sampling dichotomy and measured cell-mass assembly. It does not construct the original angular pieces, establish their overlap, prove the coarse one-tube branch, or sum their bounds. Those geometric and assembly interfaces remain outside this scalar module.

No prior module, common Lake file, verifier, registry, or published snapshot was edited.

## Verification artifacts

Commands, run in the development Lean project:

```sh
lake env lean -o .lake/build/lib/lean/LowCellAbsorption.olean LowCellAbsorption.lean
lake env lean ../low_cell_absorption_axioms.lean
```

The generated full-source audit is `audit_work/low_cell_absorption_axioms.lean`, with actual output in `audit_work/low_cell_absorption_axioms.log` and machine-checked inventory/hash result in `audit_work/low_cell_absorption_audit.json`. The source prefix, all eight named theorem entries, absence of warnings/forbidden constructs, axiom allowlist, and fresh `.olean` were checked.
