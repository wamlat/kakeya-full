import Scalar

/-! Exact scale algebra for the two operator interpolation steps. These
scalar statements do not assume or assert an interpolation theorem. All
auxiliary exponents are chosen before the tube scale. -/
namespace KakeyaFormal.OperatorScaleAlgebra
noncomputable section

def theta (a r : ℝ) : ℝ := (r-a)/(a*(r-1))
def loss (n a r e : ℝ) : ℝ :=
  (1-theta a r)*(n-a+e)/r + theta a r*(n-1)
def chosenR (a eps : ℝ) : ℝ := a+a*eps/4
def chosenError (a eps : ℝ) : ℝ := a*eps/4

theorem theta_bounds {a r : ℝ} (ha : 1 < a) (har : a < r) :
    0 < theta a r ∧ theta a r < 1 := by
  have ha0 : 0 < a := by linarith
  have hr1 : 0 < r-1 := by linarith
  dsimp [theta]
  constructor
  · exact div_pos (sub_pos.mpr har) (mul_pos ha0 hr1)
  · apply (div_lt_one (mul_pos ha0 hr1)).mpr
    nlinarith [mul_pos (show 0 < a-1 by linarith) (show 0 < r by linarith)]

theorem reciprocal_identity {a r : ℝ} (ha : 1 < a) (har : a < r) :
    1/a = (1-theta a r)/r + theta a r := by
  have ha0 : a ≠ 0 := ne_of_gt (by linarith)
  have hr0 : r ≠ 0 := ne_of_gt (by linarith)
  have hr1 : r-1 ≠ 0 := ne_of_gt (by linarith)
  dsimp [theta]
  field_simp
  ring

theorem loss_identity (n e : ℝ) {a r : ℝ} (ha : 1 < a) (har : a < r) :
    loss n a r e = (n-a)/a + (a-1)*(r-a+e)/(a*(r-1)) := by
  have ha0 : a ≠ 0 := ne_of_gt (by linarith)
  have hr0 : r ≠ 0 := ne_of_gt (by linarith)
  have hr1 : r-1 ≠ 0 := ne_of_gt (by linarith)
  dsimp [loss,theta]
  field_simp
  ring

theorem choices_positive {a eps : ℝ} (ha : 1 < a) (heps : 0 < eps) :
    a < chosenR a eps ∧ 0 < chosenError a eps := by
  have hp : 0 < a*eps/4 := by positivity
  dsimp [chosenR,chosenError]
  constructor <;> linarith

/-- The complete additional scale loss is strictly less than eps/2. The
choice depends on a and eps, and has no delta dependence. -/
theorem chosen_loss_bounds (n : ℝ) {a eps : ℝ} (ha : 1 < a) (heps : 0 < eps) :
    (n-a)/a < loss n a (chosenR a eps) (chosenError a eps) ∧
      loss n a (chosenR a eps) (chosenError a eps) < (n-a)/a+eps/2 := by
  have hchoice := choices_positive ha heps
  rw [loss_identity n _ ha hchoice.1]
  have ha0 : 0 < a := by linarith
  have hr1 : 0 < chosenR a eps-1 := by linarith [hchoice.1]
  have hnum : 0 < (a-1)*(chosenR a eps-a+chosenError a eps) := by
    apply mul_pos (by linarith)
    linarith [hchoice.1,hchoice.2]
  constructor
  · exact lt_add_of_pos_right _ (div_pos hnum (mul_pos ha0 hr1))
  · apply add_lt_add_right
    apply (div_lt_iff₀ (mul_pos ha0 hr1)).mpr
    have hp := mul_pos (mul_pos ha0 heps) (show 0 < a*eps/4 by positivity)
    dsimp [chosenR,chosenError] at *
    nlinarith

theorem chosen_scale_le (n : ℝ) {a eps δ : ℝ}
    (ha : 1 < a) (heps : 0 < eps) (hδ : 0 < δ) (hδ1 : δ ≤ 1) :
    δ^(-loss n a (chosenR a eps) (chosenError a eps)) ≤
      δ^(-((n-a)/a)-eps) := by
  apply Real.rpow_le_rpow_of_exponent_ge hδ hδ1
  have hh := (chosen_loss_bounds n ha heps).2
  linarith

end
end KakeyaFormal.OperatorScaleAlgebra
