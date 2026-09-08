# Positive-density angular proposition and fixed density normalization

All fourteen new sources are frozen, compile cleanly with matching `.olean` files, and passed exact-source production axiom audits. They contain 31 named source theorems, 52 local theorem declarations and 53 local declarations in total. Every collected axiom dependency is among `propext`, `Classical.choice`, and `Quot.sound`; there are no custom axioms, `sorry`, `admit`, `native_decide`, warnings, or error diagnostics. These are individual source results; publication still requires the parent's complete-package verifier.

## Final source-facing theorem

`PositiveWideTwoEndsPivot.from_source_inputs` proves the actual all-angle full-two-ends estimate for every positive base-density power p, including 0<p<1. It accepts precisely the new `SourceAnalyticInputs.Base` and `.Lifted` predicates: absolute-cap base and paired-error cumulative lifted input, required only at eccentricity N>=2. The proved input adapters complete coarse scales and recover the normalized estimates; no all-scale analytic conclusion is additionally assumed.

Its analytic range is m>=1, m+1<=ambient, p>0, d>=0, q>=2, D=(2m+3+d')/4<m and positive sparse-density margin (m+3)/2-D+(C-2)/3, C=(p+2q+4)/4. Thus it contains the complete source Proposition7.1 range 1<d<m, d'>0, p>0, q>=2, 1<D<m, C>2 and the stated margin. It does not assert that every such possible analytic premise is independently true.

Every fixed geometric normalization, arbitrary fixed positive original lower/upper density multiples c0,C0, fixed B>=1, alpha>0 and eps>0 precedes the actual delta, lambda, A, M, tubes and shadings. The original full shadings need only satisfy

- `c0*lambda/delta <= #Y_i <= C0*lambda/delta`;
- actual admissibility, fixed positive projective direction separation, bounded bases and full m-cap coefficient A;
- the literal full two-ends inequality for every ball and every delta<=r<=1.

The conclusion is `c*A^-1*delta^(m-D+eps)*lambda^C*M <= #union(original Y_i)`.

There is no angular-piece, sampling-outcome, marked-broadness, local-estimate, energy, desired E4 inequality or population bound supplied by the caller. The output is stronger in A than source Proposition7.1's absolute-cap conclusion. For a fixed absolute cap ceiling its inverse factor is absorbed in the fixed coefficient.

## Construction and constant quantifiers

`PositiveMarkedPivotEstimate` first extends the scalar pivot loss absorption to p>0; its proof only needs the nonnegative powers p+3 and p+4. It chooses the internal error before asking the actual positive trimming/fourth-power construction for its constant. It then calls `SourceMarkedPivotFullRange.admissible_fourth` at the previously proved explicit product radius. The radius satisfies the required post-recovery two-ends condition with 2B. Its inverse-log lower budget gives the complete original twentieth-power geometric cutoff; `PivotGeometryScale.tests_of_original_twentieth` supplies all concrete perturbation tests. This is an actual construction, not substitution of the source minimum for a smaller product radius. The subsequent first-power target only needs fixed log-conditioned kappa, so this route is legitimate for Proposition7.1.

The next ten Positive-prefixed modules copy the frozen concrete sampling/anisotropic/angular proofs under new namespaces, replacing the unnecessary `p>=1` hypothesis by `p>0` and wiring their analytic calls to the new marked theorem. Their geometric records, actual shadings, same sampling outcome, conditioning constants, four-case split, density/population retention and original-cell comparisons are unchanged. All compile under the weaker hypothesis. `PositiveTwoEndsPivot.from_base_and_lift` gives the generic actual two-ends predicate, `.from_source_inputs` accepts the absolute-cap and paired-error cumulative forms, and `PositiveTwoEndsSmallScaleInputs` adds `.from_source_small_scale_inputs` at the source N>=2 convention.

## Actual wider-row normalization

`WideTwoEndsEstimate.normalize_rows` handles arbitrary fixed density multiples before angular selection. Put a=min(c0,1/2)>0, K=ceil(a*lambda/delta), and nu=delta*K/2. Every original row contains at least K cells. A proved finite subset selection retains exactly K old cells on **every** original tube. It proves:

- all original tube indices, axes and directions remain;
- each selected full shading is contained in its own original row;
- exact strict `Comparable delta nu`;
- `nu >= a*lambda/2` and `0<nu<=1`, including the single-cell regime;
- `oldCount_i <= (C0/a)*newCount_i`.

Consequently original full two ends becomes full two ends with `Bnew=max(1,B*C0/a)`. This coefficient is fixed before delta and lambda. The all-angle theorem is applied only after this normalization, and constructs its own marked subsets from the normalized original full rows. No preservation of any old marked broadness is claimed. The final density loss is the fixed factor `(a/2)^C`, and the selected union lies inside the original union. `WideTwoEndsEstimate.from_two_ends` is generic for any proved two-ends estimate with nonnegative density power.

This closes the fixed comparable-density and positive-separation scope for the unmarked angular proposition. It does **not** close the distinct literal marked Theorem5.1 normalization: pre-existing marks with a one-tenth angular condition cannot be freely trimmed or colored without an additional proved marked-preserving argument.

## Source coverage and remaining boundaries

- Source Proposition7.1, combined.txt lines1497–1649, now has its full p>0 range and arbitrary fixed original density multiples in a concrete public theorem.
- The four source cases, scale/log comparison and original-cell overlap summation are actual proof components, not caller premises.
- Source Corollary8.2 and the published main endpoints were already in the p>=d>3 range; these new modules extend a standalone conditional statement and do not repair a failed earlier endpoint.
- SourceAnalyticInputs independently addresses the weaker source analytic quantifiers. The parent owns its audits and exact source-minimum pivot wrappers.
- Literal marked Theorem5.1 fixed comparability/separation remains separate from these modules. Measurable angular/spatial pieces have since been constructed for unit original axes in the geometry agent's `MeasurableAngularSpatial`; the comparable-length extension remains separate. No completeness percentage is inferred.

## Validation

Toolchain: Lean4.33.1, pinned mathlib `0df444a360eaa60ab8c11dca51a86af692955474`.

Each module was compiled by `lake env lean -o .lake/build/lib/lean/MODULE.olean MODULE.lean` from the development project. For every exact source, the production `verify.py` AUDIT command was appended to a separate `audit_work/MODULE_SourceAudit.lean`, and `lake env lean` was run on that full source. The resulting `MODULE_SourceAudit.log` was checked for zero diagnostics, all named source theorem coverage, every local declaration's collected axioms, and no forbidden source constructs. The aggregate machine-readable record is `positive_angular_range_audit.json`; the first eleven-module harness is `audit_positive_angular_chain.py`. The parent and finite agent have completed independent reviews with no substantive issue found. The finite review is preserved separately in `positive_angular_finite_review.md`; the parent's wider-density review is `wide_two_ends_independent_review.md`. The parent owns the integrated checkpoint verification.

| Module | Named | Theorem declarations | All declarations | SHA-256 |
|---|---:|---:|---:|---|
| `PositiveMarkedPivotEstimate.lean` | 3 | 3 | 3 | `da51c59cf87d89501c21dfdfda2fa274e2655572397e2506193283e9f75802da` |
| `PositiveSampledMarkedEstimate.lean` | 1 | 1 | 1 | `e24cf2995f073dad74410904c51380cc07899cda5913e54589379a95853ac43f` |
| `PositiveSamplingMeasurablePivot.lean` | 2 | 4 | 4 | `9eb89e77107e24f822e4bebbe0aab6e032087d4365781949d501bd5b7c87bda9` |
| `PositiveSamplingHighDensity.lean` | 3 | 3 | 3 | `c86b7bc2b6686b6fd7a7e49fe6a5f3d687576e6fb40deffb3cee1225838e05ba` |
| `PositiveSamplingOriginalCells.lean` | 1 | 8 | 8 | `acc8242b6e50ff6325b91b7d37a0abfa3c775ca95d2501da45eff9414f7ff993` |
| `PositiveAnisotropicHighDensity.lean` | 3 | 3 | 3 | `1c64200c61c233eab46df24eba23adf0cd2249c53869a6591ae395f2e1f58a76` |
| `PositiveAngularBoxHighDensity.lean` | 1 | 1 | 1 | `a2d588c92580aa603bcfcba29644a164e673fba646ec22fd4230a4f214101eb4` |
| `PositiveAngularBoxAllCases.lean` | 3 | 4 | 4 | `fe75e8df9f301b7d15e1b34b6c63388f25ca99b2cdc6b556e9af02c153a73fbc` |
| `PositiveAllAnglePivot.lean` | 3 | 3 | 3 | `7b78341d4b5142d0dfa2138a82f0e3117dc930f4c4d2a89d2fb55d2d9ca70858` |
| `PositiveAllAngleSeparation.lean` | 4 | 11 | 11 | `a72775b966825ce1ba8a13ca7f38d5edd7fc6567d4d0e6d618f3d7b643691080` |
| `PositiveTwoEndsPivot.lean` | 2 | 2 | 2 | `3ec19d098a90738a18978e41d5de46d06af345dbb9a97efe165350dfe3d0ca3a` |
| `PositiveTwoEndsSmallScaleInputs.lean` | 1 | 1 | 1 | `6b41c018121f4b516c05fae2cdb31070f78738d173cd812fca21a2f366e46ce5` |
| `WideTwoEndsEstimate.lean` | 3 | 7 | 8 | `5667f23e0b89ad3fc2906aea2b8a2365ec331ceaaf74ec679cb1dfcf0adfee51` |
| `PositiveWideTwoEndsPivot.lean` | 1 | 1 | 1 | `abb31cfa8fd7c49943469fd8bf1dbdc6683c458fa3cdff935fdfd0cc933a8da8` |
