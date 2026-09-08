import PowerKernel
import StrongTruncation
import Mathlib.Analysis.SpecialFunctions.ImproperIntegrals

/-! Actual high/low power kernels for the second interpolation stage. -/
namespace KakeyaFormal.TruncationKernels
open MeasureTheory Set StrongTruncation RestrictedInterpolation
open scoped ENNReal
noncomputable section
open Classical

theorem lintegral_Ioi_rpow {U s : ℝ} (hU : 0 < U) (hs : s < -1) :
    (∫⁻ t in Ioi U, ENNReal.ofReal (t^s)) = ENNReal.ofReal (-U^(s+1)/(s+1)) := by
  have hint := integrableOn_Ioi_rpow_of_lt hs hU
  have hnon : (0 : ℝ → ℝ) ≤ᵐ[volume.restrict (Ioi U)] (fun t => t^s) := by
    filter_upwards [self_mem_ae_restrict measurableSet_Ioi] with t ht
    exact Real.rpow_nonneg (hU.trans ht).le _
  rw [← ofReal_integral_eq_lintegral_ofReal hint hnon,integral_Ioi_rpow_of_lt hs hU]

theorem scaled_power {u c b s : ℝ} (hu : 0 < u) (hc : 0 < c) :
    u^b*(u/c)^s = c^(-s)*u^(b+s) := by
  rw [Real.div_rpow hu.le hc.le,Real.rpow_neg hc.le,Real.rpow_add hu]
  ring

theorem high_kernel_finite {u c a : ℝ} (hu : 0 < u) (hc : 0 < c) (ha : 1 < a) :
    (∫⁻ t in Ioi (0:ℝ), ENNReal.ofReal (t^(a-2)) *
      high (fun _ : Unit => ENNReal.ofReal u) (ENNReal.ofReal (c*t)) ()) =
      ENNReal.ofReal (c^(1-a)/(a-1)) * ENNReal.ofReal u ^ a := by
  have heq : (fun t : ℝ => ENNReal.ofReal (t^(a-2)) *
      high (fun _ : Unit => ENNReal.ofReal u) (ENNReal.ofReal (c*t)) ()) =
      {t | ENNReal.ofReal (c*t) < ENNReal.ofReal u}.indicator
        (fun t => ENNReal.ofReal (t^(a-2))*ENNReal.ofReal u) := by
    funext t
    by_cases h : ENNReal.ofReal (c*t) < ENNReal.ofReal u <;> simp [high,h]
  have hset : MeasurableSet {t : ℝ | ENNReal.ofReal (c*t) < ENNReal.ofReal u} :=
    measurableSet_lt (by fun_prop) measurable_const
  have hapos : 0 < a-2+1 := by linarith
  have hregion : {t : ℝ | ENNReal.ofReal (c*t) < ENNReal.ofReal u} ∩ Ioi 0 = Ioo 0 (u/c) := by
    ext t
    constructor
    · rintro ⟨h,ht⟩
      exact ⟨ht,(lt_div_iff₀ hc).mpr (by simpa [mul_comm] using (ENNReal.ofReal_lt_ofReal_iff hu).mp h)⟩
    · rintro ⟨ht,h⟩
      exact ⟨(ENNReal.ofReal_lt_ofReal_iff hu).mpr (by simpa [mul_comm] using (lt_div_iff₀ hc).mp h),ht⟩
  rw [heq,lintegral_indicator hset,Measure.restrict_restrict hset,hregion,
    lintegral_mul_const' _ _ ENNReal.ofReal_ne_top,
    lintegral_Ioo_rpow (div_pos hu hc) (show -1 < a-2 by linarith),
    ← ENNReal.ofReal_mul (by positivity : 0 ≤ (u/c)^(a-2+1)/(a-2+1)),
    ENNReal.ofReal_rpow_of_pos hu,← ENNReal.ofReal_mul (by positivity : 0 ≤ c^(1-a)/(a-1))]
  congr 1
  have hp := scaled_power (b:=1) (s:=a-1) hu hc
  simp only [Real.rpow_one] at hp
  have h1 : a-2+1 = a-1 := by ring
  have h2 : -(a-1) = 1-a := by ring
  have h3 : 1+(a-1) = a := by ring
  rw [h2,h3] at hp
  rw [h1]
  calc
    (u/c)^(a-1)/(a-1)*u = (u*(u/c)^(a-1))/(a-1) := by ring
    _ = _ := by rw [hp]; ring

theorem low_kernel_finite {u c a r : ℝ} (hu : 0 < u) (hc : 0 < c) (har : a < r) (hr : 0 < r) :
    (∫⁻ t in Ioi (0:ℝ), ENNReal.ofReal (t^(a-r-1)) *
      low (fun _ : Unit => ENNReal.ofReal u) (ENNReal.ofReal (c*t)) () ^ r) =
      ENNReal.ofReal (c^(r-a)/(r-a)) * ENNReal.ofReal u ^ a := by
  have heq : (fun t : ℝ => ENNReal.ofReal (t^(a-r-1)) *
      low (fun _ : Unit => ENNReal.ofReal u) (ENNReal.ofReal (c*t)) () ^ r) =
      {t | ENNReal.ofReal u ≤ ENNReal.ofReal (c*t)}.indicator
        (fun t => ENNReal.ofReal (t^(a-r-1))*ENNReal.ofReal u^r) := by
    funext t
    by_cases h : ENNReal.ofReal u ≤ ENNReal.ofReal (c*t)
    · simp [low,h]
    · simp [low,h,hr]
  have hset : MeasurableSet {t : ℝ | ENNReal.ofReal u ≤ ENNReal.ofReal (c*t)} :=
    measurableSet_le measurable_const (by fun_prop)
  have hregion : {t : ℝ | ENNReal.ofReal u ≤ ENNReal.ofReal (c*t)} ∩ Ioi 0 = Ici (u/c) := by
    ext t
    constructor
    · rintro ⟨h,ht⟩
      exact (div_le_iff₀ hc).mpr (by simpa [mul_comm] using (ENNReal.ofReal_le_ofReal_iff (mul_nonneg hc.le ht.le)).mp h)
    · intro h
      have ht : 0 < t := (div_pos hu hc).trans_le h
      exact ⟨ENNReal.ofReal_le_ofReal (by simpa [mul_comm] using (div_le_iff₀ hc).mp h),ht⟩
  rw [heq,lintegral_indicator hset,Measure.restrict_restrict hset,hregion,
    ← restrict_Ioi_eq_restrict_Ici,lintegral_mul_const' _ _ (ENNReal.rpow_ne_top_of_nonneg hr.le ENNReal.ofReal_ne_top),
    lintegral_Ioi_rpow (div_pos hu hc) (show a-r-1 < -1 by linarith),
    ENNReal.ofReal_rpow_of_pos hu,
    ← ENNReal.ofReal_mul (div_nonneg_of_nonpos (neg_nonpos.mpr (Real.rpow_nonneg (div_pos hu hc).le _)) (by linarith : a-r-1+1 ≤ 0)),
    ENNReal.ofReal_rpow_of_pos hu,
    ← ENNReal.ofReal_mul (by positivity : 0 ≤ c^(r-a)/(r-a))]
  congr 1
  have hp := scaled_power (b:=r) (s:=a-r) hu hc
  have h1 : a-r-1+1 = a-r := by ring
  have h2 : -(a-r) = r-a := by ring
  have h3 : r+(a-r) = a := by ring
  rw [h2,h3] at hp
  rw [h1]
  calc
    -(u/c)^(a-r)/(a-r)*u^r = (u^r*(u/c)^(a-r))/(r-a) := by
      rw [show r-a = -(a-r) by ring,div_neg]
      ring
    _ = _ := by rw [hp]; ring

end
end KakeyaFormal.TruncationKernels
