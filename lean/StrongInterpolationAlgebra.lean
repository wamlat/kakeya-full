import OperatorScaleAlgebra

/-! Exact positive-real balancing of the two truncation terms. Analytic
interpolation is proved separately; this module simplifies its actual
coefficient and the resulting powers of the tube scale. -/
namespace KakeyaFormal.StrongInterpolationAlgebra
noncomputable section

def highWeight (a r : ℝ) : ℝ := (r-a)/(r-1)
def lowWeight (a r : ℝ) : ℝ := (a-1)/(r-1)
def balance (A B r : ℝ) : ℝ := (A/B)^(1/(r-1))
def coefficient (a r : ℝ) : ℝ := 2*a/(a-1)+(2:ℝ)^r*a/(r-a)

theorem weights {a r : ℝ} (ha : 1 < a) (har : a < r) :
    0 < highWeight a r ∧ 0 < lowWeight a r ∧ highWeight a r+lowWeight a r=1 := by
  have hr : 0 < r-1 := by linarith
  refine ⟨div_pos (by linarith) hr,div_pos (by linarith) hr,?_⟩
  dsimp [highWeight,lowWeight]
  field_simp
  ring

theorem balance_pos {A B r : ℝ} (hA : 0 < A) (hB : 0 < B) : 0 < balance A B r :=
  Real.rpow_pos_of_pos (div_pos hA hB) _

theorem coefficient_pos {a r : ℝ} (ha : 1 < a) (har : a < r) :
    0 < coefficient a r := by
  have ha0 : 0 < a := by linarith
  dsimp [coefficient]
  exact add_pos (div_pos (by positivity) (by linarith))
    (div_pos (by positivity) (by linarith))

theorem mul_ratio_rpow {x y : ℝ} (hx : 0 < x) (hy : 0 < y) (s : ℝ) :
    x*(x/y)^s = x^(1+s)*y^(-s) := by
  rw [Real.div_rpow hx.le hy.le,Real.rpow_add hx,Real.rpow_one,
    Real.rpow_neg hy.le]
  ring

theorem denom_mul_ratio_rpow {x y : ℝ} (hx : 0 < x) (hy : 0 < y) (s : ℝ) :
    y*(x/y)^s = x^s*y^(1-s) := by
  rw [Real.div_rpow hx.le hy.le,Real.rpow_sub hy,Real.rpow_one]
  ring

theorem balance_high {a r A B : ℝ} (ha : 1 < a) (har : a < r)
    (hA : 0 < A) (hB : 0 < B) :
    A*(balance A B r)^(1-a) = A^(highWeight a r)*B^(lowWeight a r) := by
  have hr : r-1 ≠ 0 := ne_of_gt (by linarith)
  rw [balance,← Real.rpow_mul (div_pos hA hB).le,mul_ratio_rpow hA hB]
  have hh : 1+1/(r-1)*(1-a) = highWeight a r := by
    dsimp [highWeight]; field_simp; ring
  have hl : -(1/(r-1)*(1-a)) = lowWeight a r := by
    dsimp [lowWeight]; ring
  rw [hh,hl]

theorem balance_low {a r A B : ℝ} (ha : 1 < a) (har : a < r)
    (hA : 0 < A) (hB : 0 < B) :
    B*(balance A B r)^(r-a) = A^(highWeight a r)*B^(lowWeight a r) := by
  have hr : r-1 ≠ 0 := ne_of_gt (by linarith)
  rw [balance,← Real.rpow_mul (div_pos hA hB).le,denom_mul_ratio_rpow hA hB]
  have hh : 1/(r-1)*(r-a) = highWeight a r := by dsimp [highWeight]; ring
  have hl : 1-1/(r-1)*(r-a) = lowWeight a r := by
    dsimp [lowWeight]; field_simp; ring
  rw [hl,hh]

/-- The two actual truncation coefficients balance at a fixed positive
cutoff ratio, chosen from the endpoint constants before the test function. -/
theorem balanced_coefficient {a r A B : ℝ} (ha : 1 < a) (har : a < r)
    (hA : 0 < A) (hB : 0 < B) :
    2*a*A*(balance A B r)^(1-a)/(a-1) +
      (2:ℝ)^r*a*B*(balance A B r)^(r-a)/(r-a) =
        coefficient a r*A^(highWeight a r)*B^(lowWeight a r) := by
  calc
    _ = (2*a/(a-1))*(A*(balance A B r)^(1-a))+
        ((2:ℝ)^r*a/(r-a))*(B*(balance A B r)^(r-a)) := by ring
    _ = _ := by rw [balance_high ha har hA hB,balance_low ha har hA hB]; dsimp [coefficient]; ring

theorem moment_scale_identity (n e : ℝ) {a r : ℝ} (ha : 1 < a) (har : a < r) :
    highWeight a r*(n-1)+lowWeight a r*(n-a+e) =
      a*OperatorScaleAlgebra.loss n a r e := by
  rw [OperatorScaleAlgebra.loss_identity n e ha har]
  have ha0 : a ≠ 0 := ne_of_gt (by linarith)
  have hr : r-1 ≠ 0 := ne_of_gt (by linarith)
  dsimp [highWeight,lowWeight]
  field_simp
  ring

theorem balanced_scale (n e : ℝ) {a r C₁ C₂ δ : ℝ}
    (ha : 1 < a) (har : a < r) (hC₁ : 0 < C₁) (hC₂ : 0 < C₂) (hδ : 0 < δ) :
    (C₁*δ^(-(n-1)))^(highWeight a r)*(C₂*δ^(-(n-a+e)))^(lowWeight a r) =
      (C₁^(highWeight a r)*C₂^(lowWeight a r))*
        δ^(-a*OperatorScaleAlgebra.loss n a r e) := by
  rw [Real.mul_rpow hC₁.le (Real.rpow_nonneg hδ.le _),
    Real.mul_rpow hC₂.le (Real.rpow_nonneg hδ.le _),
    ← Real.rpow_mul hδ.le,← Real.rpow_mul hδ.le]
  have he : -(n-1)*highWeight a r + -(n-a+e)*lowWeight a r =
      -a*OperatorScaleAlgebra.loss n a r e := by
    have hh := moment_scale_identity n e ha har
    linarith
  calc
    _ = (C₁^(highWeight a r)*C₂^(lowWeight a r))*
        (δ^(-(n-1)*highWeight a r)*δ^(-(n-a+e)*lowWeight a r)) := by ring
    _ = _ := by rw [← Real.rpow_add hδ,he]

end
end KakeyaFormal.StrongInterpolationAlgebra
