# Separate finite-combinatorial audit

Audit target: `kakeya_combined (1).pdf`, dated 5 September 2026. The relevant numbered statements in this actual version are Corollary 1.1; Section 3.3, equations (3.8)–(3.10); Sections 5.5–5.7, equations (5.22)–(5.33).

## Finding

No false inequality or missing group-count/density factor was found in these finite arguments. Fourteen Lean theorems now compile, with no `sorry`, `admit`, or custom axiom. These results verify useful finite interfaces and their exact constants; they do **not** verify that the manuscript's tube geometry supplies those interfaces, or prove its maximal theorem.

## 1. Cumulative density: the single logarithm is correct

Let bins have line counts `w_j≥0`, lower densities `λ_j≥0`, total weight `Q>0`, and weighted density at least `ρ`. For every real `r≥1`, weighted convexity gives

`Q ρ^r ≤ Q(Σ w_j λ_j / Q)^r ≤ Σ w_j λ_j^r`.

If every bin union is contained in the full union of size `U` and its analytic input gives `a w_j λ_j^r ≤ U`, summation yields

`a Q ρ^r ≤ B U`,

where `B` is the number of bins. This proves that the cost is a single bin count, with the same real density power. One may add a zero-density bin for empty shadings; its estimate is vacuous because `r≥1`, and it increases the number of bins by only one. For dyadic lower endpoints, `Σw_j λ_j` is at least half the original normalized incidence mass, so `ρ=s/2` is valid. This is an alternative proof of Corollary 1.1 and does not require the preliminary density cutoff. The PDF's preliminary-cutoff proof is also correct.

The compiled `dyadic_bin_membership` theorem proves that a positive integer count `n≤Bmax` satisfies `2^log₂(n)≤n<2^(log₂(n)+1)` and its bin index belongs to `range(log₂(Bmax)+1)`. This confirms why an arbitrarily small cumulative density adds no `log(1/s)` cost. The final real-log comparison and asymptotic absorption into an arbitrary scale loss are not part of this file.

Formal theorems: `weighted_power`, `cumulative_from_bins`, `dyadic_bin_membership`.

## 2. Two proportional restorations: 3/4 and 5/8 are correct

At one position, write original multiplicity `b` and surviving multiplicity `u≤b`. At a bad position `2u<b`, surviving bad mass satisfies `u≤b−u`. Summing shows total bad surviving mass `R≤D`, the deleted mass. Therefore good mass is at least `W−D−R≥W−2D`.

For each spatial piece, let surviving total be `S_j` and good total be `G_j≤S_j`. A rejected piece has `2G_j<S_j`, hence `G_j≤S_j−G_j`. Its lost good mass is bounded by total nongood surviving mass, which is at most `D`. Thus the second selection keeps at least `W−3D`. With `D≤W/8`, the bounds are `3W/4` and `5W/8` exactly as printed.

Formal theorems: `proportional_bad_mass`, `proportional_good_mass`, `retain_good_pieces`, `restoration_constants`. They perform the actual finite threshold selection with `if`, rather than assume a conclusion about selected mass.

## 3. The nonempty floor in (5.22) correctly covers sparse inputs

For `x≥0`, the selected integer `K=max(1,floor(x))` satisfies `x/2≤K≤x+1`. This includes `x<1`; no condition equivalent to `λ²N≫1` is needed to obtain the numerical lower bound. The assertion that each geometric slab actually contains at least this many cells is a separate geometric premise and remains unformalized.

Formal theorem: `nonempty_floor_truncation`.

## 4. Grouped pruning: no number-of-groups loss

Let `r=q+e≥1`, and abbreviate the lifted analytic prefactor by

`a=c_e F⁻¹ N^(d′−d−e)`.

Index weights by `(group,color)`. Their sum is the original line count `Q`, independent of how many pivot/slab groups occur. Weighted convexity gives

`Σ U_gc ≥ a Q (I_high/(NQ))^r`.

Since a high cell occurs in at most `J` colored unions,

`H Σ U_gc ≤ J I_high ≤ J I₀`, with `I₀=ρNQ`.

Choose

`H = 2^(r+1) J N / (a ρ^(r−1))`.

There is an exact identity

`H a Q (ρ/2)^r = 2 J ρNQ = 2 J I₀`.

Thus if `I_high≥I₀/2`, the lower and upper bounds contradict each other. Fewer than half the incidences are deleted. Substituting the analytic `a` gives

`H = C_e F ρ^(1−q−e) N^(d−d′+1+e)`,

exactly equation (5.26). The factor `J` is the bounded direction-color count; **there is no factor equal to the number of groups**. Allowing empty restricted shadings is essential to applying the cumulative input with original line-count weights.

Formal theorems: `weighted_power`, `grouped_cutoff_retains_half`, `cutoff_calibration_identity`. The latter two retain the analytic lower bounds and high-cell colored-union upper bound as explicit hypotheses. No analytic Kakeya assertion is made into an axiom.

## 5. Finite support energy: injectivity is unnecessary

For each occupied `(triple,energy-position)` pair, put its nonnegative incidence multiplicity in `w_α`. The actual occupied pair set is `A`, and `p(α)` is the energy position. Cauchy–Schwarz and grouping give

`I²=(Σ_α w_α)² ≤ #A Σ_α w_α² ≤ #A Σ_p(Σ_{α:p(α)=p}w_α)²`.

If there are at most `T` triples and at most `R` occupied energy positions for each triple, then `#A≤TR`. These are two compiled theorems, including the finite counting by fibers. The square-sum comparison is in the correct direction. Several triples may share an energy position, and several incidences may share a pair; neither injectivity is required.

Given retained multiplicity `m_p≤H`, the energy is at most `HI`. Combining this with `#A≤CNE²` and `I≥I₀/2>0` yields `I₀≤2CNHE²`. This is precisely the finite algebraic closing step leading to (5.33).

Formal theorems: `support_card_by_fibers`, `finite_support_energy`, `bounded_multiplicity_energy`, `close_energy`.

The geometrically difficult hypotheses `T≲NE²` and `R≲κ⁻⁶`, including the group/slab index in the support count, are **not proved in Lean**. The supplied source carefully states that original slab labels are restored; dropping those labels would invalidate that interface.

## Formal verification record

File: `outputs/kakeya_verification/Finite.lean`.

Compiler: Lean 4.33.1, mathlib revision `0df444a360eaa60ab8c11dca51a86af692955474`.

Compilation command from the existing read-only mathlib project:

```text
/Users/ssoh/.elan/bin/lake env lean /Users/ssoh/Documents/Codex/2026-09-06/work/outputs/kakeya_verification/Finite.lean
```

Project working directory:

```text
/Users/ssoh/Documents/Codex/2026-09-05/fetch-https-prove2-me-start-md/work/prove2me_workspace
```

The final compile completed successfully, without warnings. Each of all fourteen exported theorems was checked with `#print axioms`; each depends only on Lean/mathlib's standard `propext`, `Classical.choice`, and `Quot.sound`. No geometric theorem, analytic Kakeya theorem, or unresolved inference was introduced as a custom axiom. The finite theorem names and comments explicitly identify the hypotheses supplied by the manuscript.

## Remaining scope boundary

This file does not formalize the full finite tube/cell incidence structure, construct all dyadic-bin families and apply a tube-family analytic estimate to them end to end, prove asymptotic log absorption, prove measurable conversion, verify broadness or two ends, derive lifted direction caps, prove either geometric support bound, or prove the real-cap/hairbrush/pivot/sampling interfaces. Its cutoff theorem is a conditional finite theorem whose assumptions are exposed, not a proof of the disputed analytic input. Standard classical foundation axioms are not missing mathematical hypotheses.
