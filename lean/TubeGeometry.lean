import Mathlib
import Reduction

/-!
# Quantitative tube and pivot geometry

Actual normed-space geometric interfaces for the supplied manuscript, especially
(2.1) and (5.11)–(5.31). These results do not assume a Kakeya estimate. They do
not yet prove any finite-grid packing bound, random projection probability,
angular covering theorem, or sampling theorem.
-/

namespace KakeyaAudit.TubeGeometry

open scoped RealInnerProductSpace

section LegalPivot

variable {V : Type*} [AddCommGroup V] [Module ℝ V]

/-- The legal ordering of the two first-axis samples gives an actual open-segment
pivot, including when the second-axis coordinate `c` is negative. -/
theorem legal_pivot_mem_openSegment (x u1 u2 : V) {a b c : ℝ}
    (ha : 0 < a) (hab : a < b) :
    x + a • u1 + (c * (1-a/b)) • u2 ∈
      openSegment ℝ (x+b • u1) (x+c • u2) := by
  have hb : 0 < b := lt_trans ha hab
  refine ⟨a/b, 1-a/b, div_pos ha hb, ?_, by ring, ?_⟩
  · have : a/b < 1 := (div_lt_one hb).mpr hab
    linarith
  · exact (KakeyaAudit.Reduction.pivot_convex_identity x u1 u2 a b c hb.ne').symm

/-- Closed-segment form used to count possible rounded pivots for fixed endpoints. -/
theorem legal_pivot_mem_segment (x u1 u2 : V) {a b c : ℝ}
    (ha : 0 < a) (hab : a < b) :
    x + a • u1 + (c * (1-a/b)) • u2 ∈
      segment ℝ (x+b • u1) (x+c • u2) :=
  openSegment_subset_segment ℝ _ _ (legal_pivot_mem_openSegment x u1 u2 ha hab)

end LegalPivot

/-- Quantitative separation of both convex coefficients of a legal sample. -/
theorem legal_fraction_lower_bounds {a b k B : ℝ}
    (hk : 0 < k) (ha : k ≤ a) (hgap : k ≤ b-a) (hbB : b ≤ B) :
    k/B ≤ a/b ∧ k/B ≤ 1-a/b := by
  have ha0 : 0 < a := lt_of_lt_of_le hk ha
  have hb0 : 0 < b := by linarith
  have hB0 : 0 < B := lt_of_lt_of_le hb0 hbB
  have hbase : k/B ≤ k/b := div_le_div_of_nonneg_left hk.le hb0 hbB
  constructor
  · exact hbase.trans (div_le_div_of_nonneg_right ha hb0.le)
  · have hid : 1-a/b = (b-a)/b := by field_simp
    rw [hid]
    exact hbase.trans (div_le_div_of_nonneg_right hgap hb0.le)

/-- Both pivot coefficients stay quantitatively away from zero, for either sign
of `c`; compare (5.15). The upper tube-length constant is kept as `B`. -/
theorem legal_pivot_coefficient_bounds {a b c k B : ℝ}
    (hk : 0 < k) (ha : k ≤ a) (hgap : k ≤ b-a) (hbB : b ≤ B)
    (hc : k ≤ |c|) :
    k^2/B ≤ |c*(1-a/b)| ∧ k^2/B ≤ |c-c*(1-a/b)| := by
  have ha0 : 0 < a := lt_of_lt_of_le hk ha
  have hb0 : 0 < b := by linarith
  have hB0 : 0 < B := lt_of_lt_of_le hb0 hbB
  obtain ⟨hl, hr⟩ := legal_fraction_lower_bounds hk ha hgap hbB
  have hfr : 0 ≤ 1-a/b := (div_pos hk hB0).le.trans hr
  have hfl : 0 ≤ a/b := (div_pos hk hB0).le.trans hl
  constructor
  · rw [abs_mul, abs_of_nonneg hfr]
    calc
      k^2/B = k*(k/B) := by ring
      _ ≤ |c| *(1-a/b) := mul_le_mul hc hr (div_pos hk hB0).le (abs_nonneg _)
  · have hid : c-c*(1-a/b) = c*(a/b) := by ring
    rw [hid, abs_mul, abs_of_nonneg hfl]
    calc
      k^2/B = k*(k/B) := by ring
      _ ≤ |c| *(a/b) := mul_le_mul hc hl (div_pos hk hB0).le (abs_nonneg _)

/-- The original (unperturbed) lift parameter is positive and independent of
the sign of the second-axis coordinate. -/
theorem exact_lift_parameter {a b c : ℝ} (hb : b ≠ 0)
    (hgap : b-a ≠ 0) (hc : c ≠ 0) :
    c/(c*(1-a/b)) = b/(b-a) := by
  have hf : 1-a/b ≠ 0 := by
    have hid : 1-a/b = (b-a)/b := by field_simp
    rw [hid]
    exact div_ne_zero hgap hb
  field_simp

/-- Quantitative legal range of the exact lift before pivot rounding, (5.21). -/
theorem legal_lift_range {a b c k B : ℝ}
    (hk : 0 < k) (ha : k ≤ a) (hgap : k ≤ b-a) (hbB : b ≤ B)
    (hc : c ≠ 0) :
    1+k/B ≤ c/(c*(1-a/b)) ∧ c/(c*(1-a/b)) ≤ B/k := by
  have ha0 : 0 < a := lt_of_lt_of_le hk ha
  have hgap0 : 0 < b-a := lt_of_lt_of_le hk hgap
  have hb0 : 0 < b := by linarith
  have hB0 : 0 < B := lt_of_lt_of_le hb0 hbB
  rw [exact_lift_parameter hb0.ne' hgap0.ne' hc]
  constructor
  · have hfrac : k/B ≤ a/(b-a) :=
      (div_le_div_of_nonneg_left hk.le hgap0 (by linarith : b-a ≤ B)).trans
        (div_le_div_of_nonneg_right ha hgap0.le)
    have hid : b/(b-a) = 1+a/(b-a) := by field_simp; ring
    rw [hid]
    linarith
  · calc
      b/(b-a) ≤ B/(b-a) := div_le_div_of_nonneg_right hbB hgap0.le
      _ ≤ B/k := div_le_div_of_nonneg_left hB0.le hk hgap


/-- A half-radius perturbation cannot collapse a nonzero pivot coefficient. -/
theorem perturbed_coefficient_lower_bound {u v r eta : ℝ}
    (_hr : 0 < r) (hu : r ≤ |u|) (hdiff : |v-u| ≤ eta) (heta : eta ≤ r/2) :
    r/2 ≤ |v| := by
  have htri : |u| ≤ |u-v|+|v| := by simpa using abs_add_le (u-v) v
  rw [abs_sub_comm u v] at htri
  linarith

/-- Quantitative continuity of division, with two explicit denominator bounds.
This is used for the exact lift coefficient chosen from a rounded pivot fiber. -/
theorem quotient_perturbation_bound {c u v r s eta : ℝ}
    (hr : 0 < r) (hs : 0 < s) (hu : r ≤ |u|) (hv : s ≤ |v|)
    (hdiff : |v-u| ≤ eta) :
    |c/v-c/u| ≤ |c| *eta/(r*s) := by
  have hu0 : u ≠ 0 := by intro h; simp [h] at hu; linarith
  have hv0 : v ≠ 0 := by intro h; simp [h] at hv; linarith
  have hid : c/v-c/u = c*(u-v)/(u*v) := by field_simp
  rw [hid, abs_div, abs_mul, abs_mul, abs_sub_comm u v]
  have hnum : |c| * |v-u| ≤ |c| *eta := mul_le_mul_of_nonneg_left hdiff (abs_nonneg _)
  have hden : r*s ≤ |u| *|v| := mul_le_mul hu hv hs.le (abs_nonneg _)
  exact div_le_div₀ (mul_nonneg (abs_nonneg _) ((abs_nonneg _).trans hdiff)) hnum
    (mul_pos hr hs) hden

/-- A perturbation of size `eta<=r/2` gives the inverse-square lift error. -/
theorem lift_parameter_perturbation {c u v r eta : ℝ}
    (hr : 0 < r) (hu : r ≤ |u|) (hdiff : |v-u| ≤ eta) (heta : eta ≤ r/2) :
    |c/v-c/u| ≤ 2*|c| *eta/r^2 := by
  have hv := perturbed_coefficient_lower_bound hr hu hdiff heta
  have h := quotient_perturbation_bound (c := c) hr (half_pos hr) hu hv hdiff
  convert h using 1; ring

/-- An exact ratio with a positive gap from one keeps that gap after a small
pivot perturbation. Both positivity and the quantitative upper bound are proved. -/
theorem perturbed_lift_range {c u v r eta gamma T : ℝ}
    (hr : 0 < r) (hu : r ≤ |u|) (hdiff : |v-u| ≤ eta) (heta : eta ≤ r/2)
    (hlower : 1+gamma ≤ c/u) (hupper : c/u ≤ T)
    (herror : 2*|c| *eta/r^2 ≤ gamma/2) :
    1+gamma/2 ≤ c/v ∧ c/v ≤ T+gamma/2 := by
  have herr := (lift_parameter_perturbation (c := c) hr hu hdiff heta).trans herror
  obtain ⟨hl, hu'⟩ := abs_le.mp herr
  constructor <;> linarith

/-- The perturbed lift range is deduced from the original legal sample and
explicit scalar perturbation tolerances, rather than assumed for the new line. -/
theorem legal_perturbed_lift_range {a b c v k B eta : ℝ}
    (hk : 0 < k) (ha : k ≤ a) (hgap : k ≤ b-a) (hbB : b ≤ B)
    (hc : k ≤ |c|) (hdiff : |v-c*(1-a/b)| ≤ eta)
    (heta : eta ≤ (k^2/B)/2)
    (herror : 2*|c| *eta/(k^2/B)^2 ≤ (k/B)/2) :
    1+k/(2*B) ≤ c/v ∧ c/v ≤ 2*B/k := by
  have hB0 : 0 < B := by linarith
  have hr0 : 0 < k^2/B := div_pos (sq_pos_of_pos hk) hB0
  have hc0 : c ≠ 0 := by intro h; simp [h] at hc; linarith
  obtain ⟨hlo, hhi⟩ := legal_lift_range hk ha hgap hbB hc0
  have hcoef := (legal_pivot_coefficient_bounds hk ha hgap hbB hc).1
  obtain ⟨hnewlo, hnewhi⟩ :=
    perturbed_lift_range hr0 hcoef hdiff heta hlo hhi herror
  constructor
  · convert hnewlo using 1; ring
  · have hsmall : (k/B)/2 ≤ 1 := by
      have hkb : k/B ≤ 1 := (div_le_one hB0).mpr (by linarith)
      linarith
    have hlarge : 1 ≤ B/k := (one_le_div hk).mpr (by linarith)
    calc
      c/v ≤ B/k+(k/B)/2 := hnewhi
      _ ≤ 2*(B/k) := by linarith
      _ = 2*B/k := by ring

/-- A concrete polynomial perturbation threshold suffices for the legal lift.
All lengths are normalized to at most one. The paper's stronger `delta << k^20`
condition therefore has ample room for this particular metric interface. -/
theorem normalized_perturbed_lift_range {a b c v k eta : ℝ}
    (hk : 0 < k) (hk1 : k ≤ 1) (ha : k ≤ a) (hgap : k ≤ b-a)
    (hb1 : b ≤ 1) (hc : k ≤ |c|) (hc1 : |c| ≤ 1)
    (hdiff : |v-c*(1-a/b)| ≤ eta) (heta : eta ≤ k^5/4) :
    1+k/2 ≤ c/v ∧ c/v ≤ 2/k := by
  have heta0 : 0 ≤ eta := (abs_nonneg _).trans hdiff
  have hk3 : k^3 ≤ 1 := pow_le_one₀ hk.le hk1
  have hk52 : k^5 ≤ k^2 := by
    nlinarith [mul_le_mul_of_nonneg_left hk3 (sq_nonneg k)]
  have hsmall : eta ≤ (k^2/(1:ℝ))/2 := by norm_num; nlinarith
  have herr : 2*|c| *eta/(k^2/(1:ℝ))^2 ≤ (k/(1:ℝ))/2 := by
    norm_num
    apply (div_le_iff₀ (sq_pos_of_pos (sq_pos_of_pos hk))).mpr
    nlinarith [mul_le_mul_of_nonneg_right hc1 heta0]
  simpa using legal_perturbed_lift_range hk ha hgap hb1 hc hdiff hsmall herr

section PivotResidual

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- Quantitative vector error from fixing one exact pivot coefficient in a fiber.
The actual residual is derived from the proved pivot identity and norm bounds. -/
theorem pivot_residual_bound (u1 u2 : E) {a b c v eta r B T : ℝ}
    (hb : b ≠ 0) (hr : 0 < r) (hv : r ≤ |v|)
    (hu1 : ‖u1‖ ≤ 1) (hu2 : ‖u2‖ ≤ 1)
    (hbB : |b| ≤ B) (ht : |c/v| ≤ T)
    (hdiff : |c*(1-a/b)-v| ≤ eta) :
    ‖(c/v) • (a • u1+(c*(1-a/b)) • u2)-c • u2-
      (c/v-1) • (b • u1)‖ ≤ eta*(B/r+T) := by
  have hv0 : v ≠ 0 := by intro h; simp [h] at hv; linarith
  have hB0 : 0 ≤ B := (abs_nonneg b).trans hbB
  have hT0 : 0 ≤ T := (abs_nonneg (c/v)).trans ht
  have heta0 : 0 ≤ eta := (abs_nonneg _).trans hdiff
  have hcoeff : |-b/v| ≤ B/r := by
    rw [abs_div, abs_neg]
    exact div_le_div₀ hB0 hbB hr hv
  have hnorm : ‖(-b/v) • u1+(c/v) • u2‖ ≤ B/r+T := by
    calc
      ‖(-b/v) • u1+(c/v) • u2‖ ≤ ‖(-b/v) • u1‖+‖(c/v) • u2‖ := norm_add_le _ _
      _ = |-b/v| * ‖u1‖+|c/v| * ‖u2‖ := by simp only [norm_smul, Real.norm_eq_abs]
      _ ≤ (B/r)*1+T*1 := add_le_add
        (mul_le_mul hcoeff hu1 (norm_nonneg _) (div_nonneg hB0 hr.le))
        (mul_le_mul ht hu2 (norm_nonneg _) hT0)
      _ = B/r+T := by ring
  have hid := KakeyaAudit.Reduction.pivot_defect_identity u1 u2 a b c v hb hv0
  dsimp at hid
  rw [hid, norm_smul, Real.norm_eq_abs]
  exact mul_le_mul hdiff hnorm (norm_nonneg _) heta0

/-- Replacing both endpoints and the pivot by cell centers incurs only a
linear, explicit metric error. This is the norm estimate needed before (5.31). -/
theorem rounded_pivot_residual_bound (y1 y2 z e1 e2 z0 : E)
    {t T delta R : ℝ} (ht : |t| ≤ T)
    (h1 : ‖e1-y1‖ ≤ delta) (h2 : ‖e2-y2‖ ≤ delta) (hz : ‖z0-z‖ ≤ delta)
    (hres : ‖t • z-y2-(t-1) • y1‖ ≤ R) :
    ‖(e2-e1)-t • (z0-e1)‖ ≤ R+(2*T+2)*delta := by
  have hd0 : 0 ≤ delta := (norm_nonneg _).trans h1
  have hT0 : 0 ≤ T := (abs_nonneg _).trans ht
  have htm : |t-1| ≤ T+1 := by
    have h := abs_sub t 1
    norm_num at h
    linarith
  have htz : ‖t • (z0-z)‖ ≤ T*delta := by
    rw [norm_smul, Real.norm_eq_abs]
    exact mul_le_mul ht hz (norm_nonneg _) hT0
  have hte : ‖(t-1) • (e1-y1)‖ ≤ (T+1)*delta := by
    rw [norm_smul, Real.norm_eq_abs]
    exact mul_le_mul htm h1 (norm_nonneg _) (by linarith)
  have hid : (e2-e1)-t • (z0-e1) =
      (-(t • z-y2-(t-1) • y1)+(e2-y2)-t • (z0-z))+(t-1) • (e1-y1) := by
    module
  rw [hid]
  calc
    ‖(-(t • z-y2-(t-1) • y1)+(e2-y2)-t • (z0-z))+(t-1) • (e1-y1)‖
        ≤ ‖-(t • z-y2-(t-1) • y1)+(e2-y2)-t • (z0-z)‖+
          ‖(t-1) • (e1-y1)‖ := norm_add_le _ _
    _ ≤ (‖-(t • z-y2-(t-1) • y1)+(e2-y2)‖+‖t • (z0-z)‖)+
          ‖(t-1) • (e1-y1)‖ := add_le_add (norm_sub_le _ _) (le_refl _)
    _ ≤ ((‖-(t • z-y2-(t-1) • y1)‖+‖e2-y2‖)+‖t • (z0-z)‖)+
          ‖(t-1) • (e1-y1)‖ :=
      add_le_add (add_le_add (norm_add_le _ _) (le_refl _)) (le_refl _)
    _ ≤ ((R+delta)+T*delta)+(T+1)*delta := by
      exact add_le_add (add_le_add (add_le_add (by simpa only [norm_neg] using hres) h2) htz) hte
    _ = R+(2*T+2)*delta := by ring

omit [NormedSpace ℝ E] in
/-- A known separation survives rounding both points. This supplies the lower
norm in the parameter-recovery lemma from an actual geometric separation. -/
theorem separation_after_rounding (a b a0 b0 : E) {r delta : ℝ}
    (hsep : r ≤ ‖a-b‖) (ha : ‖a-a0‖ ≤ delta) (hb : ‖b0-b‖ ≤ delta) :
    r-2*delta ≤ ‖a0-b0‖ := by
  have hid : a-b = (a-a0)+(a0-b0)+(b0-b) := by abel
  have h : ‖a-b‖ ≤ ‖a-a0‖+‖a0-b0‖+‖b0-b‖ := by
    rw [hid]
    exact (norm_add_le _ _).trans (add_le_add (norm_add_le _ _) (le_refl _))
  linarith

/-- The two fully rounded instances of one endpoint/pivot triple have close
lift parameters. Unlike a bare scalar identity, both norm-error and metric
separation inputs are propagated through the endpoint rounding. -/
theorem rounded_triple_parameter_bound (y1 y2 z y1' y2' z' e1 e2 z0 : E)
    {s t T delta R r : ℝ} (hr : 0 < r) (hdelta : delta ≤ r/4)
    (hsep : r ≤ ‖z-y1‖)
    (h1 : ‖e1-y1‖ ≤ delta) (h2 : ‖e2-y2‖ ≤ delta) (hz : ‖z0-z‖ ≤ delta)
    (h1' : ‖e1-y1'‖ ≤ delta) (h2' : ‖e2-y2'‖ ≤ delta) (hz' : ‖z0-z'‖ ≤ delta)
    (hsT : |s| ≤ T) (htT : |t| ≤ T)
    (hsres : ‖s • z-y2-(s-1) • y1‖ ≤ R)
    (htres : ‖t • z'-y2'-(t-1) • y1'‖ ≤ R) :
    |t-s| ≤ 4*(R+(2*T+2)*delta)/r := by
  have hround := separation_after_rounding z y1 z0 e1 hsep
    (by simpa only [norm_sub_rev] using hz) h1
  have hsep' : r/2 ≤ ‖z0-e1‖ := by linarith
  have hs := rounded_pivot_residual_bound y1 y2 z e1 e2 z0 hsT h1 h2 hz hsres
  have ht := rounded_pivot_residual_bound y1' y2' z' e1 e2 z0 htT h1' h2' hz' htres
  have h := KakeyaAudit.Reduction.parameter_interval_length (z0-e1) (e2-e1)
    s t (r/2) (R+(2*T+2)*delta) (half_pos hr) hsep' hs ht
  convert h using 1; ring

end PivotResidual

section Projection

variable {E F : Type*}
variable [NormedAddCommGroup E] [NormedSpace ℝ E]
variable [NormedAddCommGroup F] [NormedSpace ℝ F]

/-- Exact longitudinal metric under a linear projection of an affine axis. -/
theorem projected_axis_distance (P : E →L[ℝ] F) (x v : E) (s t : ℝ) :
    ‖P (x+t • v)-P (x+s • v)‖ = |t-s| * ‖P v‖ := by
  have hid : P (x+t • v)-P (x+s • v) = (t-s) • P v := by
    simp only [map_add, map_smul]
    module
  rw [hid, norm_smul, Real.norm_eq_abs]

/-- A noncollapsed projected direction bounds longitudinal collapse for points
on the exact axis. The finite grid-cell counting step is not included. -/
theorem projected_axis_parameter_bound (P : E →L[ℝ] F) (x v : E)
    {s t c r : ℝ} (hc : 0 < c) (hv : c ≤ ‖P v‖)
    (himage : ‖P (x+t • v)-P (x+s • v)‖ ≤ r) :
    |t-s| ≤ r/c := by
  apply (le_div_iff₀ hc).mpr
  calc
    |t-s| *c ≤ |t-s| *‖P v‖ := mul_le_mul_of_nonneg_left hv (abs_nonneg _)
    _ ≤ r := by rw [projected_axis_distance] at himage; exact himage

/-- Projected points within `delta` of an affine tube axis satisfy the same
longitudinal bound with the explicit transverse error `2*K*delta`.
This is the geometric collapse interface in Lemma 2.1. -/
theorem projected_tube_parameter_bound (P : E →L[ℝ] F) (x v e1 e2 : E)
    {s t c r K delta : ℝ} (hc : 0 < c) (hv : c ≤ ‖P v‖)
    (hK : ‖P‖ ≤ K) (he1 : ‖e1‖ ≤ delta) (he2 : ‖e2‖ ≤ delta)
    (himage : ‖P (x+t • v+e1)-P (x+s • v+e2)‖ ≤ r) :
    |t-s| ≤ (r+2*K*delta)/c := by
  have hK0 : 0 ≤ K := (norm_nonneg P).trans hK
  have he1p : ‖P e1‖ ≤ K*delta := by
    exact (P.le_opNorm e1).trans (mul_le_mul hK he1 (norm_nonneg _) hK0)
  have he2p : ‖P e2‖ ≤ K*delta := by
    exact (P.le_opNorm e2).trans (mul_le_mul hK he2 (norm_nonneg _) hK0)
  have hid : P (x+t • v)-P (x+s • v) =
      (P (x+t • v+e1)-P (x+s • v+e2))-(P e1-P e2) := by
    simp only [map_add]
    abel
  apply projected_axis_parameter_bound P x v hc hv
  calc
    ‖P (x+t • v)-P (x+s • v)‖ =
        ‖(P (x+t • v+e1)-P (x+s • v+e2))-(P e1-P e2)‖ := by rw [hid]
    _ ≤ ‖P (x+t • v+e1)-P (x+s • v+e2)‖ + ‖P e1-P e2‖ := norm_sub_le _ _
    _ ≤ r+(‖P e1‖+‖P e2‖) := add_le_add himage (norm_sub_le _ _)
    _ ≤ r+2*K*delta := by linarith

end Projection

section Orthogonal

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

/-- Orthogonal component relative to a unit vector. -/
def transverse (u v : E) : E := v - (inner ℝ u v) • u

/-- The displayed component is perpendicular to the unit stem direction. -/
theorem transverse_inner_zero (u v : E) (hu : ‖u‖ = 1) :
    inner ℝ u (transverse u v) = 0 := by
  simp [transverse, inner_sub_right, inner_smul_right, hu]

/-- Orthogonal removal is a contraction, proved from Pythagoras. -/
theorem transverse_norm_le (u v : E) (hu : ‖u‖ = 1) :
    ‖transverse u v‖ ≤ ‖v‖ := by
  have hz : inner ℝ (transverse u v) u = 0 := by
    calc
      inner ℝ (transverse u v) u = inner ℝ u (transverse u v) := real_inner_comm _ _
      _ = 0 := transverse_inner_zero u v hu
  have horth : inner ℝ (transverse u v) ((inner ℝ u v) • u) = 0 := by
    rw [inner_smul_right, hz, mul_zero]
  have hp := norm_add_sq_eq_norm_sq_add_norm_sq_real horth
  have hid : transverse u v + (inner ℝ u v) • u = v := by
    simp [transverse]
  rw [hid] at hp
  nlinarith [norm_nonneg (transverse u v), norm_nonneg v,
    sq_nonneg ‖(inner ℝ u v) • u‖]

/-- Explicit squared transverse size: for unit vectors it is one minus the
squared cosine, making the hypothesis a genuine angular-transversality condition. -/
theorem transverse_norm_sq (u v : E) (hu : ‖u‖ = 1) :
    ‖transverse u v‖ ^ 2 = ‖v‖ ^ 2 - (inner ℝ u v) ^ 2 := by
  rw [transverse, norm_sub_sq_real]
  simp only [inner_smul_right, real_inner_comm v u, norm_smul, Real.norm_eq_abs,
    hu, mul_one, sq_abs]
  ring

/-- A pivot's distance from every point of the first axis dominates its exact
orthogonal component. No line-distance estimate is assumed as a hypothesis. -/
theorem pivot_transverse_distance (x u v : E) (a d s : ℝ) (hu : ‖u‖ = 1) :
    |d| * ‖transverse u v‖ ≤ ‖(x+a • u+d • v)-(x+s • u)‖ := by
  have hid : transverse u ((x+a • u+d • v)-(x+s • u)) =
      d • transverse u v := by
    simp only [transverse, inner_sub_right, inner_add_right, inner_smul_right,
      real_inner_self_eq_norm_sq, hu, one_pow, mul_one]
    module
  have h := transverse_norm_le u ((x+a • u+d • v)-(x+s • u)) hu
  rw [hid, norm_smul, Real.norm_eq_abs] at h
  exact h

/-- The `k^3/B` distance bound in (5.15), now for every point on the stem axis. -/
theorem legal_pivot_stem_separation (x u1 u2 : E) {a b c k B s : ℝ}
    (hu1 : ‖u1‖ = 1) (hk : 0 < k) (ha : k ≤ a)
    (hgap : k ≤ b-a) (hbB : b ≤ B) (hc : k ≤ |c|)
    (htrans : k ≤ ‖transverse u1 u2‖) :
    k^3/B ≤ ‖(x+a • u1+(c*(1-a/b)) • u2)-(x+s • u1)‖ := by
  have hcoef := (legal_pivot_coefficient_bounds hk ha hgap hbB hc).1
  have hB0 : 0 < B := by linarith
  calc
    k^3/B = (k^2/B)*k := by ring
    _ ≤ |c*(1-a/b)| * ‖transverse u1 u2‖ :=
      mul_le_mul hcoef htrans hk.le (abs_nonneg _)
    _ ≤ _ := pivot_transverse_distance x u1 u2 a (c*(1-a/b)) s hu1

end Orthogonal

end KakeyaAudit.TubeGeometry

#print axioms KakeyaAudit.TubeGeometry.legal_pivot_mem_openSegment
#print axioms KakeyaAudit.TubeGeometry.normalized_perturbed_lift_range
#print axioms KakeyaAudit.TubeGeometry.rounded_triple_parameter_bound
#print axioms KakeyaAudit.TubeGeometry.projected_tube_parameter_bound
#print axioms KakeyaAudit.TubeGeometry.legal_pivot_stem_separation
