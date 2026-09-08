# Uniform direction and cap normalization

AnisotropicDirections.lean and AnisotropicCap.lean are cleanly compiled. They use the actual normalized image of each original direction under the genuine affine spatial map's linear part.

For unit original directions v,w in an angular*tau projective cap about a unit u, with angular≥0 and0<tau≤1, the proved inverse estimate is

pd(v,w) ≤ 4(1+2angular)^2 * tau * pd(transformed(v),transformed(w)).

The proof includes antipodal signs. On the small angular chart, a nonzero-head bound and exact graph-slope scaling reduce to the independently verified graph chart. Outside the small chart, contraction of the inverse linear map supplies a coarse normalization bound, and the lower bound on tau absorbs the missing scale factor. No injectivity, derivative estimate or chart regularity is assumed.

Consequences for an actual transformed family:

- Original separation delta becomes delta/[4(1+2angular)^2*tau].
- Original CapBound(delta,m,A) becomes CapBound(delta/tau,m,packingConstant(k)*A*[8(1+2angular)^2]^m), for ambient dimension k+1, m≥0,A≥0 and0<delta≤tau≤1.

The cap center is arbitrary. A nonempty new cap is pulled back around one actual family member. If the original radius is≤1, the original cap hypothesis applies in its stated domain. If it exceeds1, the independent finite global projective cap cover bounds the whole original family. This prevents an unproved extension of the original cap condition beyond radius1.

The transformed family is explicitly built from the actual integer-translate unit tubes of AnisotropicRescaling. Its new shadings are arbitrary in these direction-only results; admissibility and retention are provided by the separate actual-grid extension. The local angular condition quantifies over every original tube index. A spatial/angular group stored using empty shadings on excluded original indices must therefore first be restricted/reindexed to its participating tube indices; empty shadings alone do not remove directions from a CapBound count.

Lean4.33.1, Mathlib commit0df444a360eaa60ab8c11dca51a86af692955474. From audit_work/formalization, compile each module with `lake env lean -o .lake/build/lib/lean/MODULE.olean MODULE.lean`. Full-source axiom files/logs are anisotropic_directions_axioms.{lean,log} and anisotropic_cap_axioms.{lean,log} in audit_work. All22+2 theorem declarations have only standard dependencies propext, Classical.choice and Quot.sound. No sorry or custom axioms.
