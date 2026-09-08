import RestrictedStrong
import StrongInterpolation
import StrongInterpolationAlgebra
import OperatorNormConversion
import KakeyaOperatorL1

/-! The actual strong Kakeya operator estimate. The two interpolation stages
are proved and instantiated on the original-position operator; all auxiliary
exponents and constants are fixed before the scale and input function. -/
namespace KakeyaFormal.OperatorStrongEstimate
open MeasureTheory KakeyaOperator StrongInterpolationAlgebra
open scoped ENNReal
noncomputable section
set_option maxHeartbeats 1000000

/-- A positive real L1 constant with the exact ambient scale convention. -/
theorem l1_constant (k : ℕ) :
    ∃ C : ℝ, 0 < C ∧ ∀ {δ : ℝ}, 0 < δ →
      ∀ f : Space (k+1) → ℝ≥0∞,
        (∫⁻ v, maximal δ f v ∂sphereMeasure (k+1)) ≤
          ENNReal.ofReal (C*δ^(-(((k+1:ℕ):ℝ)-1)))*(∫⁻ x, f x ∂volume) := by
  let C := (KakeyaOperatorL1.scaleConstant k).toReal+1
  have hC : 0 < C := by dsimp [C]; positivity
  have hbound : KakeyaOperatorL1.scaleConstant k ≤ ENNReal.ofReal C := by
    rw [← ENNReal.ofReal_toReal (KakeyaOperatorL1.scaleConstant_finite k)]
    apply ENNReal.ofReal_le_ofReal
    dsimp [C]
    linarith
  refine ⟨C,hC,?_⟩
  intro δ hδ f
  have h := (KakeyaOperatorL1.maximal_lintegral_scale_le hδ f).trans
    (mul_le_mul' (mul_le_mul' hbound le_rfl) le_rfl)
  have heq : (ENNReal.ofReal (δ^k))⁻¹ = ENNReal.ofReal (δ^(-(((k+1:ℕ):ℝ)-1))) := by
    rw [← ENNReal.ofReal_inv_of_pos (pow_pos hδ k)]
    congr 1
    rw [Real.rpow_neg hδ.le]
    congr 1
    simp only [Nat.cast_add,Nat.cast_one,add_sub_cancel_right,Real.rpow_natCast]
  rw [heq,← ENNReal.ofReal_mul hC.le] at h
  exact h

/-- Both analytic stages and the actual L1/positive/measurability inputs
are discharged. The remaining exponent is given by the exact scalar loss. -/
theorem interpolated_moment {k : ℕ} {a r e : ℝ}
    (hestimate : OperatorRestrictedWeak.Estimate (k+1) a)
    (ha : 1 < a) (har : a < r) (he : 0 < e) :
    ∃ K : ℝ, 0 < K ∧ ∀ {δ : ℝ}, 0 < δ → δ ≤ 1 →
      ∀ f : Space (k+1) → ℝ≥0∞, Measurable f →
        (∫⁻ v, maximal δ f v^a ∂sphereMeasure (k+1)) ≤
          ENNReal.ofReal (K*δ^(-a*OperatorScaleAlgebra.loss ((k+1:ℕ):ℝ) a r e))*
            (∫⁻ x, f x^a ∂volume) := by
  obtain ⟨C₁,hC₁,h₁⟩ := l1_constant k
  obtain ⟨C₂,hC₂,hᵣ⟩ := RestrictedStrong.from_estimate hestimate (by linarith) har he
  let K := StrongInterpolationAlgebra.coefficient a r*C₁^(highWeight a r)*C₂^(lowWeight a r)
  have hK : 0 < K := by
    have hc := StrongInterpolationAlgebra.coefficient_pos ha har
    dsimp [K]
    positivity
  refine ⟨K,hK,?_⟩
  intro δ hδ hδ1 f hf
  let A := C₁*δ^(-(((k+1:ℕ):ℝ)-1))
  let B := C₂*δ^(-(((k+1:ℕ):ℝ)-a+e))
  have hA : 0 < A := by dsimp [A]; positivity
  have hB : 0 < B := by dsimp [B]; positivity
  have hh := StrongInterpolation.strong_interpolation
    (volume : Measure (Space (k+1))) (sphereMeasure (k+1))
    (RestrictedOperatorLaws.positive_laws hδ)
    (fun g hg => KakeyaOperatorMeasurability.maximal_measurable hδ g hg)
    ha har hA.le hB.le (balance_pos (r:=r) hA hB)
    (fun g _ => h₁ hδ g) (fun g hg => hᵣ hδ hδ1 g hg) hf
  have hc : StrongInterpolation.coefficient a r A B (balance A B r) =
      K*δ^(-a*OperatorScaleAlgebra.loss ((k+1:ℕ):ℝ) a r e) := by
    rw [StrongInterpolation.coefficient,balanced_coefficient ha har hA hB]
    calc
      _ = StrongInterpolationAlgebra.coefficient a r*
          (A^(highWeight a r)*B^(lowWeight a r)) := by ring
      _ = _ := by
        dsimp only [A,B]
        rw [balanced_scale ((k+1:ℕ):ℝ) e ha har hC₁ hC₂ hδ]
        dsimp [K]
        ring
  rwa [hc] at hh

end
end KakeyaFormal.OperatorStrongEstimate
