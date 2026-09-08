# Separate review: legal parameter selection and actual tube samples

Reviewed the frozen `LegalParameterSelection.lean` and `LegalTubeSamples.lean` on 6 September 2026. No mathematical defect, incorrect constant, circular abundance hypothesis, or density-dependent loss was found in their stated conclusions. This is a separate source-level review within the same AI-assisted development, not an independent human endorsement.

## What is actually proved

`finite_quantile` chooses an occupied label, handles repeated parameter values, and proves both strict-below and weak-below population bounds. It does not assume injective projection or distinct coordinates.

`early_late_on_positive_branch` starts with a branch of size at least `|S|/3`. Choosing the `|S|/8` quantile, the initial portion through one κ-window has size less than `|S|/8+|S|/16`. Thus the late portion is larger than `7|S|/48`, which is sufficient for the stated `|S|/8`. Early coordinates are at least κ, and every late coordinate exceeds every early one by κ. The argument correctly permits boundary ties.

`positive_or_negative_branch` and `oriented_early_late` choose a single orientation for the entire first-axis selection, not a separate sign per sample. The second-axis remote set has at least half the original population. The actual product set therefore contains at least

`(|S|/8)(|S|/8)(|T|/2) ≥ density³/128`

ordered triples. Its entries remain original labels; no projection-injectivity assumption or integer rounding of the density is used.

`projected_interval_nonconcentration` derives a κ-window bound from the original physical-ball condition. A label whose coordinate is within κ of t lies within `width·δ+κ ≤ (width+1)κ` of the corresponding shifted-axis point. The assumptions explicitly put that test radius in `[δ,1]` and make its two-ends factor at most `1/16`. This is a genuine geometric reduction, not an assumed interval count.

`shifted_tube_projection` uses actual membership of the vertex and sample point in one original unit tube. If their axis parameters are s and t, the shifted-axis error is at most twice the tube radius, and `|s−t|≤1`. Orthogonal projection can only decrease that error; the actual projected coordinate is bounded by `1+2 radius`.

The main `legal_triples_from_tubes` correctly substitutes the shifted-axis width `2·width` into the interval lemma. Consequently the required physical radius is `(2·width+1)κ`, exactly as stated. It obtains at least `(λ/δ)³/128` original-label triples and, using `δ≤1` and nonnegative width, the uniform raw coordinate bound `1+2·width`.

## Exact relation to combined equation (5.11)

For each output sample set, put `a₀=sign·f(early)`, `b=sign·f(late)`, and `c=g(remote)`. Since `κ≥δ>0`, the proved inequalities imply `0<a₀<b≤1+2·width`, `a₀≥κ`, `b−a₀≥κ`, and `|c|≥κ`. Reversing the first unit direction by that same fixed sign preserves the actual projected points. Negative c is permitted by the manuscript and the pivot formulas; the absence of a second orientation choice is appropriate.

The theorem does **not** supply transversality of the two directions, manufacture the common vertex from marked incidences, impose `b≤1`, construct pivots/rounded outputs, or prove a per-projection-interval multiplicity bound. These are distinct interfaces. The common-vertex membership is explicitly assumed, the transversality belongs to the prior marked-angle construction, and the bound here is deliberately the raw `1+2·width`. A later normalization must carry its constants and injective label map through the existing pivot witness types. Calling this an abundance theorem for the coordinate part of (5.11) is accurate; calling it the entire transverse pivot construction would be too broad.

The cases of repeated projected coordinates, sparse nonintegral lower-density thresholds, endpoint ties, and either first-axis orientation were checked. There is no unstated assumption that `λ/δ` is an integer or exceeds a fixed positive threshold. Where very small populations are incompatible with the physical nonconcentration hypothesis, the incompatibility is explicit in that hypothesis rather than concealed by a counting step.
