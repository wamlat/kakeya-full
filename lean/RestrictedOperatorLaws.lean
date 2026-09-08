import RestrictedInterpolation
import KakeyaOperatorLaws

/-! The finite interpolation laws are discharged by the actual Kakeya
operator, with no abstract operator-law premise at the application boundary. -/
namespace KakeyaFormal.RestrictedOperatorLaws
open MeasureTheory KakeyaOperator KakeyaOperatorLaws RestrictedInterpolation
open scoped ENNReal NNReal
noncomputable section

theorem positive_laws {n : ℕ} {δ : ℝ} (hδ : 0 < δ) :
    PositiveLaws (maximal (n:=n) δ) where
  zero := maximal_zero δ
  monotone := fun _ _ h v => maximal_mono δ h v
  add_le := fun _ g hf _ v => maximal_add_le δ hf g v
  mul_const := fun c f _ => funext (fun v => maximal_finite_mul δ c ENNReal.coe_ne_top f v)
  bounded := fun _ _ _ h v => maximal_le_const hδ h v

end
end KakeyaFormal.RestrictedOperatorLaws
