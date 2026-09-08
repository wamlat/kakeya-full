import Mathlib

/-!
# Scalar analytic reductions for the supplied Kakeya manuscript

These are unconditional facts about real numbers (and, below, real vector spaces).
They verify scalar steps used in Sections 5, 7, 8 and 9. They do not assert a
geometric tube estimate, the existence of a localization, or a maximal theorem.
All positive-base and exponent hypotheses are explicit.
-/

namespace KakeyaAudit.Reduction

theorem localized_density_gain {nu rho C D : ℝ}
    (hnu : 0 < nu) (hnr : nu ≤ rho) (hr : rho ≤ 1) :
    nu ^ max D C ≤ nu ^ C * rho ^ (D - C) := by
  have hr0 : 0 < rho := lt_of_lt_of_le hnu hnr
  by_cases hCD : C ≤ D
  · rw [max_eq_left hCD]
    calc
      nu ^ D = nu ^ C * nu ^ (D-C) := by
        rw [← Real.rpow_add hnu]; congr 1; ring
      _ ≤ nu ^ C * rho ^ (D-C) :=
        mul_le_mul_of_nonneg_left
          (Real.rpow_le_rpow hnu.le hnr (sub_nonneg.mpr hCD))
          (Real.rpow_nonneg hnu.le _)
  · rw [max_eq_right (le_of_not_ge hCD)]
    have hpow : 1 ≤ rho ^ (D-C) := by
      simpa using Real.rpow_le_rpow_of_exponent_ge hr0 hr
        (show D-C ≤ 0 by linarith)
    simpa using mul_le_mul_of_nonneg_left hpow (Real.rpow_nonneg hnu.le C)

theorem localized_density_gain_with_constant {nu rho K C D : ℝ}
    (hnu : 0 < nu) (hr0 : 0 < rho) (hr : rho ≤ 1)
    (hK : 1 ≤ K) (hnr : nu ≤ K*rho) :
    nu ^ max D C ≤ K ^ max (D-C) 0 * (nu ^ C * rho ^ (D-C)) := by
  by_cases hCD : C ≤ D
  · rw [max_eq_left hCD, max_eq_left (sub_nonneg.mpr hCD)]
    calc
      nu ^ D = nu ^ C * nu ^ (D-C) := by
        rw [← Real.rpow_add hnu]; congr 1; ring
      _ ≤ nu ^ C * (K*rho) ^ (D-C) := mul_le_mul_of_nonneg_left
        (Real.rpow_le_rpow hnu.le hnr (sub_nonneg.mpr hCD))
        (Real.rpow_nonneg hnu.le _)
      _ = _ := by rw [Real.mul_rpow (by linarith) hr0.le]; ring
  · have hDC : D ≤ C := le_of_not_ge hCD
    rw [max_eq_right hDC, max_eq_right (sub_nonpos.mpr hDC), Real.rpow_zero, one_mul]
    have hpow : 1 ≤ rho ^ (D-C) := by
      simpa using Real.rpow_le_rpow_of_exponent_ge hr0 hr (sub_nonpos.mpr hDC)
    simpa using mul_le_mul_of_nonneg_left hpow (Real.rpow_nonneg hnu.le C)

theorem occupancy_factor {w P : ℝ} (hw : 0 < w) (hw1 : w ≤ 1) (hP : 1 ≤ P) :
    1 ≤ w ^ (1-P) := by
  simpa using Real.rpow_le_rpow_of_exponent_ge hw hw1
    (show 1-P ≤ 0 by linarith)

theorem occupancy_gain {w lam P : ℝ}
    (hw : 0 < w) (hw1 : w ≤ 1) (hlam : 0 ≤ lam) (hP : 1 ≤ P) :
    lam ^ P ≤ w * (lam / w) ^ P := by
  have hid : w * (lam / w) ^ P = lam ^ P * w ^ (1-P) := by
    rw [Real.div_rpow hlam hw.le, Real.rpow_sub hw, Real.rpow_one]
    ring
  rw [hid]
  simpa using mul_le_mul_of_nonneg_left (occupancy_factor hw hw1 hP)
    (Real.rpow_nonneg hlam P)

theorem angular_factor {tau D m beta e : ℝ}
    (ht : 0 < tau) (ht1 : tau ≤ 1) (hb : beta ≤ m-D) (he : 0 ≤ e) :
    1 ≤ tau ^ (D-m+beta-e) := by
  simpa using Real.rpow_le_rpow_of_exponent_ge ht ht1
    (show D-m+beta-e ≤ 0 by linarith)

theorem density_error_absorption {N lam s e : ℝ}
    (hN : 0 < N) (hlam : N ^ (-s) ≤ lam) (he : 0 ≤ e) :
    N ^ (-s*e) ≤ lam ^ e := by
  rw [Real.rpow_mul hN.le]
  exact Real.rpow_le_rpow (Real.rpow_nonneg hN.le _) hlam he

theorem fiber_density_gain {lam sigma c q e : ℝ}
    (hl : 0 < lam) (hc : 0 < c) (hq : 2 ≤ q) (he : 0 ≤ e)
    (hs : c * lam ^ (2 : ℝ) ≤ sigma) :
    c ^ (q+e-2) * lam ^ (2*q+2+2*e) ≤
      lam ^ (6 : ℝ) * sigma ^ (q+e-2) := by
  have hpow := Real.rpow_le_rpow
    (mul_nonneg hc.le (Real.rpow_nonneg hl.le (2 : ℝ))) hs
    (show 0 ≤ q+e-2 by linarith)
  have hid : lam ^ (6 : ℝ) * (c * lam ^ (2 : ℝ)) ^ (q+e-2) =
      c ^ (q+e-2) * lam ^ (2*q+2+2*e) := by
    rw [Real.mul_rpow hc.le (Real.rpow_nonneg hl.le (2 : ℝ)), ← Real.rpow_mul hl.le]
    rw [← mul_assoc, mul_comm (lam ^ (6 : ℝ)), mul_assoc, ← Real.rpow_add hl]
    congr 2
    ring
  rw [← hid]
  exact mul_le_mul_of_nonneg_left hpow (Real.rpow_nonneg hl.le (6 : ℝ))

theorem finite_depth_transfer {delta lam n d D p P eps : ℝ}
    (hd : 0 < delta) (hd1 : delta ≤ 1)
    (hl : 0 < lam) (hl1 : lam ≤ 1)
    (hgap : D-d ≤ eps/2) (hp : p ≤ P) :
    delta ^ (n-D+eps) * lam ^ P ≤ delta ^ (n-d+eps/2) * lam ^ p := by
  exact mul_le_mul
    (Real.rpow_le_rpow_of_exponent_ge hd hd1 (by linarith))
    (Real.rpow_le_rpow_of_exponent_ge hl hl1 hp)
    (Real.rpow_nonneg hl.le _) (Real.rpow_nonneg hd.le _)

theorem choose_two_ends_exponent {eps P : ℝ} (he : 0 < eps) (hP : 0 < P) :
    ∃ alpha : ℝ, 0 < alpha ∧ alpha ≤ 1/4 ∧ alpha*P < eps/3 := by
  refine ⟨min (1/4) (eps/(6*P)), lt_min (by norm_num) (div_pos he (by positivity)),
    min_le_left _ _, ?_⟩
  have h := mul_le_mul_of_nonneg_right (min_le_right (1/4 : ℝ) (eps/(6*P))) hP.le
  have hid : eps/(6*P)*P = eps/6 := by field_simp
  rw [hid] at h
  linarith

theorem small_density_one_tube {delta lam D P : ℝ}
    (hd : 0 < delta) (hd1 : delta ≤ 1)
    (hl : 0 < lam) (hld : lam ≤ delta) (hP : 1 ≤ P) (hDP : D ≤ P) :
    1 ≤ delta ^ (D-1) * lam ^ (1-P) := by
  have hlpow : delta ^ (1-P) ≤ lam ^ (1-P) :=
    Real.rpow_le_rpow_of_nonpos hl hld (by linarith)
  have hbase : 1 ≤ delta ^ (D-P) := by
    simpa using Real.rpow_le_rpow_of_exponent_ge hd hd1 (sub_nonpos.mpr hDP)
  calc
    1 ≤ delta ^ (D-P) := hbase
    _ = delta ^ (D-1) * delta ^ (1-P) := by
      rw [← Real.rpow_add hd]; congr 1; ring
    _ ≤ _ := mul_le_mul_of_nonneg_left hlpow (Real.rpow_nonneg hd.le _)

/-! Section 9.3: the interpolation arithmetic, without asserting any operator bound. -/
theorem interpolation_weight {a r : ℝ} (ha : a ≠ 0) (hr : r ≠ 0) (hr1 : r ≠ 1) :
    1/a = (1-(r-a)/(a*(r-1)))/r + (r-a)/(a*(r-1)) := by
  field_simp
  ring

theorem interpolation_loss_identity {n a r e : ℝ}
    (ha : a ≠ 0) (hr : r ≠ 0) (hr1 : r ≠ 1) :
    (1-(r-a)/(a*(r-1)))*(n-a+e)/r + (r-a)/(a*(r-1))*(n-1) =
      (n-a)/a + (a-1)*(r-a+e)/(a*(r-1)) := by
  field_simp
  ring

theorem interpolation_loss_budget {n a eps : ℝ} (ha : 1 < a) (heps : 0 < eps) :
    ∃ r e : ℝ, a < r ∧ 0 < e ∧
      (1-(r-a)/(a*(r-1)))*(n-a+e)/r + (r-a)/(a*(r-1))*(n-1) <
        (n-a)/a + eps := by
  let r := a+eps/4
  let e := eps/4
  have hr : a < r := by dsimp [r]; linarith
  have he : 0 < e := by dsimp [e]; linarith
  have hden : 0 < a*(r-1) := mul_pos (by linarith) (by linarith)
  have hcoef : a-1 ≤ a*(r-1) := by
    nlinarith [mul_nonneg (show 0 ≤ a-1 by linarith) (show 0 ≤ r-1 by linarith)]
  have hsum : 0 ≤ r-a+e := by linarith
  have hbound : (a-1)*(r-a+e)/(a*(r-1)) ≤ r-a+e := by
    apply (div_le_iff₀ hden).mpr
    nlinarith [mul_le_mul_of_nonneg_right hcoef hsum]
  refine ⟨r,e,hr,he,?_⟩
  rw [interpolation_loss_identity (by linarith) (by linarith) (by linarith)]
  dsimp [r,e] at hbound ⊢
  linarith

/-! The exact vector identity behind (5.31). No rounding estimate is assumed here. -/
section Pivot
variable {V : Type*} [AddCommGroup V] [Module ℝ V]

theorem pivot_convex_identity (x u1 u2 : V) (a b c : ℝ) (hb : b ≠ 0) :
    x + a • u1 + (c * (1-a/b)) • u2 =
      (a/b) • (x+b • u1) + (1-a/b) • (x+c • u2) := by
  have hab : a/b*b = a := by field_simp
  simp only [smul_add, smul_smul]
  rw [hab]
  module

theorem pivot_defect_identity (u1 u2 : V) (a b c ustar : ℝ)
    (hb : b ≠ 0) (hu : ustar ≠ 0) :
    let u := c * (1-a/b)
    let t := c/ustar
    t • (a • u1 + u • u2) - c • u2 - (t-1) • (b • u1) =
      (u-ustar) • ((-b/ustar) • u1 + t • u2) := by
  dsimp
  have hcoef : c/ustar*a-(c/ustar-1)*b = (c*(1-a/b)-ustar)*(-b/ustar) := by
    field_simp
    ring
  have hcoef2 : c/ustar*(c*(1-a/b))-c = (c*(1-a/b)-ustar)*(c/ustar) := by
    field_simp
  simp only [smul_add, smul_smul]
  linear_combination (norm := module) hcoef • u1 + hcoef2 • u2

end Pivot

/-! Quantitative stability of the parameter reconstructed from (5.31).
The cell-counting/packing consequences of this metric estimate are not formalized here. -/
section Stability
variable {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]

theorem parameter_stability (v w : V) (s t A B : ℝ)
    (hv : A ≤ ‖v‖) (hs : ‖w-s • v‖ ≤ B) (ht : ‖w-t • v‖ ≤ B) :
    |t-s| * A ≤ 2*B := by
  have hid : (t-s) • v = (w-s • v) - (w-t • v) := by module
  calc
    |t-s| * A ≤ |t-s| * ‖v‖ := mul_le_mul_of_nonneg_left hv (abs_nonneg _)
    _ = ‖(t-s) • v‖ := by rw [norm_smul, Real.norm_eq_abs]
    _ = ‖(w-s • v) - (w-t • v)‖ := by rw [hid]
    _ ≤ ‖w-s • v‖ + ‖w-t • v‖ := norm_sub_le _ _
    _ ≤ 2*B := by linarith

theorem parameter_interval_length (v w : V) (s t A B : ℝ)
    (hA : 0 < A) (hv : A ≤ ‖v‖) (hs : ‖w-s • v‖ ≤ B) (ht : ‖w-t • v‖ ≤ B) :
    |t-s| ≤ 2*B/A := by
  exact (le_div_iff₀ hA).mpr (parameter_stability v w s t A B hv hs ht)

end Stability

end KakeyaAudit.Reduction
