# Separate geometry review: original marked lengths

Read-only review of the four frozen source files below and their `marked_length_normalization_progress.md` report. No source edits or new axioms. Compilation/dependency validation remains the author's and parent's separately recorded audit.

| Source | SHA256 |
|---|---|
| `MarkedLengthNormalization.lean` | `5ea82c09f6b8cf490214ba7289a622a61f1c4773be9606ebe7daa58ebd9ab861` |
| `MarkedLengthInput.lean` | `3425378039d183f61a4ed092ca9530264e9f144cd9c4c450f3c7bd48c3d89066` |
| `MarkedLengthAlgebra.lean` | `39a313f959f9424cf83c06284233f2f23ca3dd2469117c4491c0cc536021968c` |
| `SourceMarkedLengths.lean` | `9b7c8685193c4bb78e95523947f316b64840ffa7ba558f4bf7b5dbfe3c764e8e` |

No substantive mathematical or statement defect found. Each original direction, tube index, full integer row, marked integer row and occupied integer union is preserved by the single dilation `W=max(1,lengthUpper)`. The physical centers and bases change by the same factor, with mesh `delta/W`; density `lambda/W` therefore gives exactly the original row bounds and marked total. Per-index actual axis lengths enter the carrier premise. A negative or zero length cannot create a spurious nonempty positive-density example; the marked input requires positive population and positive lower row counts.

Cap inheritance uses the original bottom-scale cap test for radii between the new and old meshes. It does not infer new-scale separation merely from a cap bound. The actual original separation becomes sufficient at the smaller mesh, and base bounds scale to `R/W`. For full two ends, the pullback ball has radius `W*r`: the original hypothesis applies up to radius one; total row count handles larger radii. `0<=alpha<=1` justifies `W^alpha<=W`, so the final multiplier of B is fixed independently of alpha.

The minimum-scale identity places the entire fixed normalization cost inside the concentration numerator. Explicitly, if `c_unit` is the small constant for the normalized width and `C_grid` is its full-two-ends normalization factor, the original choice uses `c*=c_unit/(C_grid*W)` in both occurrences of `c*min(theta,1/100,(c*/B)^(1/alpha))`. Its relationship to the normalized theorem at `B*W` is proved exactly; there is no extraction of an alpha-dependent factor as a uniform constant. The original twentieth-power cutoff implies the actual finer-mesh cutoff.

The final transport uses the support exponent zero only to express that this *second*, length-dilation step does not inflate the integer union. It leaves the actual ambient collision exponent `5(ambient-1)+6q+12` unchanged. The earlier marked-grid refinement's fixed union inflation is already accounted for in `SourceMarkedNormalization`. Both transports preserve the displayed powers of xi, logarithm, N, lambda and S. The source notation theorem has positive T,c chosen before all original alpha, B, theta, xi, lambda, N, population and sample data; its only analytic premises are the exact source-style Base and Lifted predicates.

Source-scope qualification: the source permits constants depending on fixed normalization data immediately after (5.3). Under that convention this is the manuscript-form choice of the unspecified small constant. It is not a proof using an independently prescribed, earlier width-only constant uniformly across arbitrary density/separation/length normalizations. If that stronger reading of the subscript `c_k` were intended, it must remain a distinct assertion: changing the concentration numerator has ratio raised to `1/alpha`, so an alpha-uniform comparison is unavailable in general.
