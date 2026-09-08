import KakeyaOperatorMeasurability

/-! Convert actual nonnegative moment inequalities to Mathlib's eLpNorm,
including the exact scale exponent and the absolute-value real-input model. -/
namespace KakeyaFormal.OperatorNormConversion
open MeasureTheory
open scoped ENNReal
noncomputable section

theorem norm_eq_moment {X : Type*} [MeasurableSpace X] (μ : Measure X)
    (f : X → ℝ≥0∞) {a : ℝ} (ha : 0 < a) :
    eLpNorm f (ENNReal.ofReal a) μ = (∫⁻ x, f x^a ∂μ)^(1/a) := by
  rw [eLpNorm_eq_lintegral_rpow_enorm_toReal (ENNReal.ofReal_pos.mpr ha).ne'
    ENNReal.ofReal_ne_top]
  simp only [ENNReal.toReal_ofReal ha.le,enorm_eq_self]

theorem norm_ofReal_abs {X : Type*} [MeasurableSpace X] (μ : Measure X)
    (f : X → ℝ) (p : ℝ≥0∞) :
    eLpNorm (fun x => ENNReal.ofReal |f x|) p μ = eLpNorm f p μ := by
  simp only [eLpNorm,eLpNorm',eLpNormEssSup,enorm_eq_self,Real.enorm_eq_ofReal_abs]

theorem moment_to_norm {X Y : Type*} [MeasurableSpace X] [MeasurableSpace Y]
    (μ : Measure X) (ν : Measure Y) (f : X → ℝ≥0∞) (g : Y → ℝ≥0∞)
    {a A : ℝ} (ha : 0 < a) (hA : 0 < A)
    (h : (∫⁻ y, g y^a ∂ν) ≤ ENNReal.ofReal A*(∫⁻ x, f x^a ∂μ)) :
    eLpNorm g (ENNReal.ofReal a) ν ≤ ENNReal.ofReal (A^(1/a))*eLpNorm f (ENNReal.ofReal a) μ := by
  have ha' : 0 ≤ 1/a := by positivity
  have hh := ENNReal.rpow_le_rpow h ha'
  rw [ENNReal.mul_rpow_of_nonneg _ _ ha',ENNReal.ofReal_rpow_of_pos hA] at hh
  simpa only [norm_eq_moment _ _ ha] using hh

/-- Taking the a-th root divides the entire moment scale loss by a. This
holds for infinite input/output moments without real-valued integral conversion. -/
theorem scaled_moment_to_norm {X Y : Type*} [MeasurableSpace X] [MeasurableSpace Y]
    (μ : Measure X) (ν : Measure Y) (f : X → ℝ≥0∞) (g : Y → ℝ≥0∞)
    {a C δ s : ℝ} (ha : 0 < a) (hC : 0 < C) (hδ : 0 < δ)
    (h : (∫⁻ y, g y^a ∂ν) ≤ ENNReal.ofReal (C*δ^(-a*s))*(∫⁻ x, f x^a ∂μ)) :
    eLpNorm g (ENNReal.ofReal a) ν ≤
      ENNReal.ofReal (C^(1/a)*δ^(-s))*eLpNorm f (ENNReal.ofReal a) μ := by
  have hcoef : 0 < C*δ^(-a*s) := by positivity
  have hh := moment_to_norm μ ν f g ha hcoef h
  have heq : (C*δ^(-a*s))^(1/a) = C^(1/a)*δ^(-s) := by
    rw [Real.mul_rpow hC.le (Real.rpow_nonneg hδ.le _),← Real.rpow_mul hδ.le]
    congr 2
    field_simp
  rwa [heq] at hh

end
end KakeyaFormal.OperatorNormConversion
