import SamplingNormalizedMeans

/-! Exact, unweighted expectations for the probabilities in source (6.5).
These results retain the original density constants and total marked mass. -/
namespace KakeyaFormal.SamplingRawMeans
open Finset SamplingNormalizedMeans SamplingSupport SamplingMeans KakeyaSamplingApplication MeasureTheory
open scoped BigOperators
noncomputable section
open Classical

variable {n M : ℕ} {F : TubeFamily (n+1) M} {Full G : Fin M → Set (Space (n+1))}
variable {δ width R lam c₀ C₀ xi B alpha K beta : ℝ}
variable (h : Input F Full G δ width R lam c₀ C₀ xi B alpha K beta)
include h

/-- The raw full means retain literally c0 and C0. -/
theorem full_mean_bounds (i : Fin M) :
    c₀*lam/δ ≤ fullMean (rawFull F Full δ width R) i ∧
      fullMean (rawFull F Full δ width R) i ≤ C₀*lam/δ :=
  fullMean_density F.tube Full h.scale_pos h.scale_le_one h.width_nonneg
    h.bounded h.full_subset h.full_measurable h.full_mass i

/-- Every positive-measure marked cell is included, so no mass is lost in the
raw expectation identity. -/
theorem marked_mean_eq :
    (∑ z : support F.tube Full δ width R, markedMean (rawMarked F Full G δ width R) z) =
      (∑ i, (volume : Measure (Space (n+1))).real (G i))/δ^(n+1) :=
  marked_total_mean F.tube Full G h.scale_pos h.scale_le_one h.width_nonneg
    h.bounded h.full_subset h.marked_measurable h.marked_subset

theorem marked_mean_lower : xi*lam*(M:ℝ)/δ ≤
    ∑ z : support F.tube Full δ width R, markedMean (rawMarked F Full G δ width R) z := by
  rw [marked_mean_eq h]
  have hlo := div_le_div_of_nonneg_right h.marked_mass (pow_pos h.scale_pos (n+1)).le
  have hid : (xi*lam*δ^n*(M:ℝ))/δ^(n+1) = xi*lam*(M:ℝ)/δ := by
    rw [pow_succ]
    field_simp [h.scale_pos.ne']
  rwa [hid] at hlo

/-- Raw ball expectations require only the original full two-ends condition
at radii between delta and one. The coefficient is independent of alpha≤1. -/
theorem ball_test {J : ℕ} (ha1 : alpha ≤ 1) (hbottom : δ ≤ Localization.radius J 0)
    (i : Fin M) (t : SamplingBallTests.Test (support F.tube Full δ width R) J) :
    4*ballMean (rawFull F Full δ width R) (SamplingBallTests.mask δ) i t ≤
      ballCoefficient n*B*(SamplingBallTests.testRadius t)^alpha*
        fullMean (rawFull F Full δ width R) i := by
  have hg1 : 1 ≤ 1+((n+1:ℕ):ℝ)/2 := by
    have hn := Nat.cast_nonneg (α := ℝ) (n+1)
    linarith
  have hg : (1+((n+1:ℕ):ℝ)/2)^alpha ≤ 1+((n+1:ℕ):ℝ)/2 := by
    simpa only [Real.rpow_one] using Real.rpow_le_rpow_of_exponent_le hg1 ha1
  have hB0 : 0 ≤ B := zero_le_one.trans h.two_ends_constant
  have hmu : 0 ≤ fullMean (rawFull F Full δ width R) i :=
    (div_nonneg (mul_nonneg h.lower_constant_pos.le h.density_pos.le) h.scale_pos.le).trans (full_mean_bounds h i).1
  have hrad : 0 ≤ SamplingBallTests.testRadius t := by
    have hh := (SamplingBallTests.radius_bounds hbottom t).1
    linarith [h.scale_pos]
  have hball := SamplingMeans.ballMean_two_ends F.tube Full h.scale_pos h.scale_le_one h.width_nonneg
    h.two_ends_constant h.two_ends_exponent hbottom h.bounded h.full_subset h.full_measurable h.two_ends i t
  calc
    _ ≤ 4*(B*(1+((n+1:ℕ):ℝ)/2)^alpha*(SamplingBallTests.testRadius t)^alpha*
        fullMean (rawFull F Full δ width R) i) :=
      mul_le_mul_of_nonneg_left hball (by norm_num)
    _ ≤ 4*(B*(1+((n+1:ℕ):ℝ)/2)*(SamplingBallTests.testRadius t)^alpha*
        fullMean (rawFull F Full δ width R) i) := by gcongr
    _ = _ := by unfold ballCoefficient; ring

/-- The source theta uses K itself; no row-comparability ratio is necessary
for the original probabilities. -/
theorem cap_test (htest : δ ≤ 2*SamplingTheta.choice K beta)
    (z : ↥(support F.tube Full δ width R)) (a : Fin M) :
    1000*capMean (rawMarked F Full G δ width R)
      (SamplingCapTests.cap F (SamplingTheta.choice K beta)) z a ≤
        markedMean (rawMarked F Full G δ width R) z := by
  apply SamplingMeans.capMean_admissible F G _ h.scale_pos htest
    (by linarith [SamplingTheta.choice_le_hundredth K beta]) _ h.marked_measurable h.broadness z a
  simpa only [mul_assoc] using SamplingTheta.cap_budget h.broadness_constant h.broadness_exponent

end
end KakeyaFormal.SamplingRawMeans
