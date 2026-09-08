import OperatorNorm

/-! Main actual Kakeya operator norm conclusions. Both the measurable-shading
theorem and its operator deduction are proved; no published custom axiom,
interpolation theorem, geometric cover or operator-law premise remains. -/
namespace KakeyaFormal.MainOperator
noncomputable section

/-- The actual six-dimensional L^(33/8) maximal-operator norm estimate, for
every positive epsilon and every a.e.-measurable real input. -/
theorem six_first : OperatorNorm.Estimate 6 (33/8) :=
  OperatorNorm.from_shading (k:=5) MainMaximal.six_first (by norm_num)

/-- The main all-dimensional algebraic exponent, now as the actual strong
operator norm assertion with the exact delta^(1-n/a-epsilon) loss. -/
theorem endpoint_formula {n : ℕ} (hn : 6 ≤ n) :
    OperatorNorm.Estimate n (3+(2-Real.sqrt 2)*((n:ℝ)-4)) := by
  have hroot : 0 < 2-Real.sqrt 2 := by
    have hs := Real.sq_sqrt (show (0:ℝ) ≤ 2 by norm_num)
    have hh := Real.sqrt_nonneg (2:ℝ)
    nlinarith
  have hdim : 0 ≤ (n:ℝ)-4 := by
    have hh : (6:ℝ) ≤ n := by exact_mod_cast hn
    linarith
  have ha : 1 < 3+(2-Real.sqrt 2)*((n:ℝ)-4) := by
    nlinarith [mul_nonneg hroot.le hdim]
  cases n with
  | zero => omega
  | succ k => exact OperatorNorm.from_shading (MainMaximal.endpoint_formula hn) ha

theorem endpoint {n : ℕ} (hn : 6 ≤ n) :
    OperatorNorm.Estimate n (KakeyaScalar.limitProfile ((n:ℝ)-1)) := by
  have heq : KakeyaScalar.limitProfile ((n:ℝ)-1) = 3+(2-Real.sqrt 2)*((n:ℝ)-4) := by
    dsimp [KakeyaScalar.limitProfile,KakeyaScalar.slopeLimit]
    ring
  rw [heq]
  exact endpoint_formula hn

theorem six_endpoint : OperatorNorm.Estimate 6 (7-2*Real.sqrt 2) := by
  apply OperatorNorm.from_shading (k:=5) MainMaximal.six_endpoint
  have hs := Real.sq_sqrt (show (0:ℝ) ≤ 2 by norm_num)
  have hh := Real.sqrt_nonneg (2:ℝ)
  nlinarith

theorem eight_endpoint : OperatorNorm.Estimate 8 (11-4*Real.sqrt 2) := by
  apply OperatorNorm.from_shading (k:=7) MainMaximal.eight_endpoint
  have hs := Real.sq_sqrt (show (0:ℝ) ≤ 2 by norm_num)
  have hh := Real.sqrt_nonneg (2:ℝ)
  nlinarith

theorem six_diagonal_limit : OperatorNorm.Estimate 6 (29/7) :=
  OperatorNorm.from_shading (k:=5) MainMaximal.six_diagonal_limit (by norm_num)

theorem eight_diagonal_limit : OperatorNorm.Estimate 8 (37/7) :=
  OperatorNorm.from_shading (k:=7) MainMaximal.eight_diagonal_limit (by norm_num)

end
end KakeyaFormal.MainOperator
