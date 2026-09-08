import Mathlib.Analysis.SpecialFunctions.Pow.Integral
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic

/-! Exact nonnegative power kernels for constructive interpolation. -/
namespace KakeyaFormal.RestrictedInterpolation
open MeasureTheory Set
open scoped ENNReal NNReal
noncomputable section

/-- The exact positive power integral used for each dyadic band. -/
theorem lintegral_Ioo_rpow {U s : ℝ} (hU : 0 < U) (hs : -1 < s) :
    ∫⁻ t in Ioo 0 U, ENNReal.ofReal (t^s) = ENNReal.ofReal (U^(s+1)/(s+1)) := by
  have hint : IntegrableOn (fun t : ℝ => t^s) (Ioo 0 U) volume :=
    (intervalIntegrable_iff_integrableOn_Ioo_of_le hU.le).mp
      (intervalIntegral.intervalIntegrable_rpow' hs)
  have hnon : (0 : ℝ → ℝ) ≤ᵐ[volume.restrict (Ioo 0 U)] (fun t => t^s) := by
    filter_upwards [self_mem_ae_restrict measurableSet_Ioo] with t ht
    exact Real.rpow_nonneg ht.1.le _
  rw [← ofReal_integral_eq_lintegral_ofReal hint hnon,
    ← integral_Ioc_eq_integral_Ioo, ← intervalIntegral.integral_of_le hU.le,
    integral_rpow (Or.inl hs)]
  simp only [Real.zero_rpow (show s+1 ≠ 0 by linarith), sub_zero]

theorem cutoff_power_identity {t U b r : ℝ} (ht : 0 < t) (hU : 0 < U) :
    (t/U)^(-b)*t^(r-1) = U^b*t^(r-b-1) := by
  rw [Real.div_rpow ht.le hU.le, Real.rpow_neg hU.le, div_eq_mul_inv, inv_inv]
  calc
    t^(-b)*U^b*t^(r-1) = U^b*(t^(-b)*t^(r-1)) := by ring
    _ = _ := by rw [← Real.rpow_add ht]; congr 2; ring

theorem lintegral_cutoff_power {U b r : ℝ} (hU : 0 < U) (hbr : b < r) :
    ∫⁻ t in Ioo 0 U, ENNReal.ofReal ((t/U)^(-b)*t^(r-1)) =
      ENNReal.ofReal (U^r/(r-b)) := by
  have hid : (∫⁻ t in Ioo 0 U, ENNReal.ofReal ((t/U)^(-b)*t^(r-1))) =
      ∫⁻ t in Ioo 0 U, ENNReal.ofReal (U^b)*ENNReal.ofReal (t^(r-b-1)) := by
    apply setLIntegral_congr_fun measurableSet_Ioo
    intro t ht
    dsimp only
    rw [cutoff_power_identity (b:=b) (r:=r) ht.1 hU, ENNReal.ofReal_mul (Real.rpow_nonneg hU.le _)]
  rw [hid, lintegral_const_mul' _ _ ENNReal.ofReal_ne_top,
    lintegral_Ioo_rpow hU (show -1 < r-b-1 by linarith)]
  rw [← ENNReal.ofReal_mul (Real.rpow_nonneg hU.le _)]
  congr 1
  have he : r-b-1+1 = r-b := by ring
  rw [he, ← mul_div_assoc, ← Real.rpow_add hU]
  congr 2
  ring

end
end KakeyaFormal.RestrictedInterpolation
