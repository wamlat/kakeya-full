import LengthOperatorGeometry

/-! Pointwise domination of the actual variable-length supremum by one
actual unit-tube operator at the same delta and one common dilated input. -/
namespace KakeyaFormal.LengthOperatorBound
open MeasureTheory Set SamplingGeometry WidthNormalization KakeyaOperator LengthOperatorGeometry
open scoped ENNReal
noncomputable section

theorem carrier_volume_lower {k : ℕ} (T : UnitTube (k+1))
    {s length width δ : ℝ} (hs : 0 < s) (hsL : s ≤ length)
    (hsw : s ≤ width) (hδ : 0 ≤ δ) :
    ENNReal.ofReal (s^(k+1))*(volume : Measure (Space (k+1))) (T.carrier δ) ≤
      volume (lengthCarrier T length (width*δ)) := by
  have hh := ENNReal.ofReal_le_ofReal (LengthTubeVolume.volume_lower T hs hsL hsw hδ)
  simpa only [ENNReal.ofReal_mul (pow_nonneg hs.le _),Measure.real,
    ENNReal.ofReal_toReal (TubeVolume.carrier_finite T δ),
    ENNReal.ofReal_toReal (LengthTubeVolume.carrier_finite T length (width*δ))] using hh

theorem average_le_unit {k : ℕ} {s W length width δ : ℝ}
    (hs : 0 < s) (hW : 0 < W) (hsL : s ≤ length) (hsw : s ≤ width)
    (hLW : length ≤ W) (hwW : width ≤ W) (hδ : 0 ≤ δ)
    (f : Space (k+1) → ℝ≥0∞) (b : Space (k+1)) (v : Direction (k+1)) :
    LengthOperatorGeometry.average δ width length f b v ≤
      ENNReal.ofReal (W^(k+1)/s^(k+1))*
        KakeyaOperator.average δ (fun x => f (W • x)) (W⁻¹ • b) v := by
  let S := lengthCarrier (tube v b) length (width*δ)
  let U := (tube v (W⁻¹ • b)).carrier δ
  have ht : normalizedTube (tube v b) W = tube v (W⁻¹ • b) := by
    simp [WidthNormalization.normalizedTube,Rescaling.tube,Rescaling.rescale,KakeyaOperator.tube,UnitTube.axisPoint]
  have hsub : normalizedSet W S ⊆ U := by
    simpa only [S,U,ht] using LengthTubeVolume.containing_unit_carrier (tube v b) hW hLW hwW hδ
  have hnum := lintegral_mono_set (μ:=volume) (f:=fun x => f (W • x)) hsub
  have hlo := carrier_volume_lower (tube v b) hs hsL hsw hδ
  have hden := mul_le_mul' (le_refl (ENNReal.ofReal ((W^(k+1))⁻¹))) hlo
  have hid : (W^(k+1))⁻¹*s^(k+1)=s^(k+1)/W^(k+1) := by ring
  rw [← mul_assoc,← ENNReal.ofReal_mul (inv_nonneg.mpr (pow_nonneg hW.le _)),hid,
    ← normalized_measure hW S] at hden
  rw [TubeIsometryVolume.carrier_volume_eq (tube v b) (tube v (W⁻¹ • b)) δ] at hden
  have havg : LengthOperatorGeometry.average δ width length f b v =
      (∫⁻ x in normalizedSet W S, f (W • x) ∂volume)/volume (normalizedSet W S) := by
    rw [normalized_set_integral hW,normalized_measure hW]
    exact (ENNReal.mul_div_mul_left _ _ (by positivity) ENNReal.ofReal_ne_top).symm
  rw [havg]
  have hh := ENNReal.div_le_div hnum hden
  refine hh.trans_eq ?_
  change (∫⁻ x in U, f (W • x) ∂volume)/
    (ENNReal.ofReal (s^(k+1)/W^(k+1))*volume U) = _
  have hr : 0 < s^(k+1)/W^(k+1) := div_pos (pow_pos hs _) (pow_pos hW _)
  rw [div_eq_mul_inv,ENNReal.mul_inv (Or.inl (ENNReal.ofReal_pos.mpr hr).ne')
    (Or.inl ENNReal.ofReal_ne_top),← ENNReal.ofReal_inv_of_pos hr]
  have he : (s^(k+1)/W^(k+1))⁻¹ = W^(k+1)/s^(k+1) := by field_simp
  rw [he]
  change _ = ENNReal.ofReal (W^(k+1)/s^(k+1))*
    ((∫⁻ x in U, f (W • x) ∂volume)/volume U)
  simp only [div_eq_mul_inv,mul_left_comm]

theorem maximal_le_unit {k : ℕ} {lower upper width δ : ℝ}
    (hl : 0 < lower) (hw : 0 < width) (hδ : 0 ≤ δ)
    (f : Space (k+1) → ℝ≥0∞) (v : Direction (k+1)) :
    LengthOperatorGeometry.maximal lower upper width δ f v ≤
      ENNReal.ofReal ((MaximalLengths.upperScale upper width)^(k+1)/
        (MaximalLengths.lowerScale lower width)^(k+1))*
      KakeyaOperator.maximal δ (fun x => f (MaximalLengths.upperScale upper width • x)) v := by
  obtain ⟨hs,_,hsl,hsw,hW,huW,hwW⟩ := MaximalLengths.scale_bounds (lengthUpper:=upper) hl hw
  have hWp : 0 < MaximalLengths.upperScale upper width := zero_lt_one.trans_le hW
  apply iSup_le
  intro length
  apply iSup_le
  intro b
  exact (average_le_unit hs hWp (hsl.trans length.property.1) hsw
    (length.property.2.trans huW) hwW hδ f b v).trans
    (mul_le_mul' le_rfl (le_iSup (fun b : Space (k+1) =>
      KakeyaOperator.average δ (fun x => f (MaximalLengths.upperScale upper width • x)) b v) _))

end
end KakeyaFormal.LengthOperatorBound
