import TubeIsometryVolume

/-! The actual general Kakeya operator has an L1 bound from global mass and
the fixed tube volume. Extended-real inequalities include infinite input mass;
operator measurability is not needed for these extended nonnegative integral inequalities. -/
namespace KakeyaFormal.KakeyaOperatorL1
open MeasureTheory Set KakeyaOperator TubeIsometryVolume
open scoped ENNReal
noncomputable section

def coefficient (k : ℕ) (δ : ℝ) : ℝ≥0∞ :=
  sphereMeasure (k+1) univ / referenceVolume k δ

theorem average_le_global {k : ℕ} (δ : ℝ) (f : Space (k+1) → ℝ≥0∞)
    (b : Space (k+1)) (v : Direction (k+1)) :
    average δ f b v ≤ (∫⁻ x, f x ∂volume) / referenceVolume k δ := by
  rw [average_fixed_denominator]
  exact ENNReal.div_le_div_right (setLIntegral_le_lintegral _ _) _

theorem maximal_le_global {k : ℕ} (δ : ℝ) (f : Space (k+1) → ℝ≥0∞)
    (v : Direction (k+1)) :
    maximal δ f v ≤ (∫⁻ x, f x ∂volume) / referenceVolume k δ :=
  iSup_le (fun b => average_le_global δ f b v)

/-- Actual sphere integration of the original all-position maximal operator. -/
theorem maximal_lintegral_le {k : ℕ} (δ : ℝ) (f : Space (k+1) → ℝ≥0∞) :
    (∫⁻ v, maximal δ f v ∂sphereMeasure (k+1)) ≤
      coefficient k δ * (∫⁻ x, f x ∂volume) := by
  calc
    _ ≤ ∫⁻ _v : Direction (k+1),
        (∫⁻ x, f x ∂volume) / referenceVolume k δ ∂sphereMeasure (k+1) :=
      lintegral_mono (fun v => maximal_le_global δ f v)
    _ = _ := by rw [lintegral_const]; simp [coefficient,div_eq_mul_inv,mul_comm,mul_left_comm,mul_assoc]

theorem coefficient_finite (k : ℕ) {δ : ℝ} (hδ : 0 < δ) : coefficient k δ ≠ ∞ := by
  apply ENNReal.div_ne_top
  · change (volume : Measure (Space (k+1))).toSphere univ ≠ ∞
    exact measure_ne_top _ _
  · exact (referenceVolume_pos k hδ).ne'

def lowerVolumeConstant (k : ℕ) : ℝ :=
  TubeVolume.unitBallVolume (k+1) / (2:ℝ)^(k+2)

theorem lowerVolumeConstant_pos (k : ℕ) : 0 < lowerVolumeConstant k := by
  exact div_pos (TubeVolume.unitBallVolume_pos (k+1)) (by positivity)

theorem referenceVolume_lower (k : ℕ) {δ : ℝ} (hδ : 0 < δ) :
    ENNReal.ofReal (lowerVolumeConstant k * δ^k) ≤ referenceVolume k δ := by
  apply (ENNReal.ofReal_le_iff_le_toReal (referenceVolume_finite k δ)).mpr
  have h := TubeVolume.carrier_volume_lower (referenceTube k) hδ
  have hid : (TubeVolume.unitBallVolume (k+1)/(2:ℝ)^(k+1+1))*δ^(k+1)/δ =
      lowerVolumeConstant k * δ^k := by
    change lowerVolumeConstant k * δ^(k+1)/δ = lowerVolumeConstant k * δ^k
    rw [pow_succ,← mul_assoc,mul_div_cancel_right₀ _ hδ.ne']
  exact hid ▸ h

def scaleConstant (k : ℕ) : ℝ≥0∞ :=
  sphereMeasure (k+1) univ / ENNReal.ofReal (lowerVolumeConstant k)

theorem scaleConstant_finite (k : ℕ) : scaleConstant k ≠ ∞ := by
  apply ENNReal.div_ne_top
  · change (volume : Measure (Space (k+1))).toSphere univ ≠ ∞
    exact measure_ne_top _ _
  · exact (ENNReal.ofReal_pos.mpr (lowerVolumeConstant_pos k)).ne'

theorem coefficient_scale_le (k : ℕ) {δ : ℝ} (hδ : 0 < δ) :
    coefficient k δ ≤ scaleConstant k * (ENNReal.ofReal (δ^k))⁻¹ := by
  have h := ENNReal.div_le_div_left (referenceVolume_lower k hδ)
    (sphereMeasure (k+1) univ)
  simp only [ENNReal.ofReal_mul (lowerVolumeConstant_pos k).le,div_eq_mul_inv] at h
  rw [ENNReal.mul_inv (Or.inl (ENNReal.ofReal_pos.mpr (lowerVolumeConstant_pos k)).ne')
      (Or.inl ENNReal.ofReal_ne_top)] at h
  simpa [coefficient,scaleConstant,div_eq_mul_inv,mul_assoc] using h

/-- The fixed-dimensional L1 loss is at most a constant times δ to the power
minus k, where the actual ambient dimension is k+1. -/
theorem maximal_lintegral_scale_le {k : ℕ} {δ : ℝ} (hδ : 0 < δ)
    (f : Space (k+1) → ℝ≥0∞) :
    (∫⁻ v, maximal δ f v ∂sphereMeasure (k+1)) ≤
      scaleConstant k * (ENNReal.ofReal (δ^k))⁻¹ * (∫⁻ x, f x ∂volume) :=
  (maximal_lintegral_le δ f).trans (mul_le_mul' (coefficient_scale_le k hδ) le_rfl)

theorem normMaximal_lintegral_le {k : ℕ} (δ : ℝ) (f : Space (k+1) → ℝ) :
    (∫⁻ v, normMaximal δ f v ∂sphereMeasure (k+1)) ≤
      coefficient k δ * (∫⁻ x, ENNReal.ofReal |f x| ∂volume) :=
  maximal_lintegral_le δ (fun x => ENNReal.ofReal |f x|)

end
end KakeyaFormal.KakeyaOperatorL1
