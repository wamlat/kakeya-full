import GaussianMatrix

/-! The actual Gaussian matrix as a continuous linear map on input vectors.
Its operator norm is bounded by the Euclidean norm of all original entries. -/
namespace KakeyaFormal.GaussianLinearOperator
open GaussianMatrix
open scoped RealInnerProductSpace
noncomputable section

def linear {rows cols : ℕ} (ω : Sample rows cols) : Space cols →ₗ[ℝ] Space rows where
  toFun := fun v => projection v ω
  map_add' := by
    intro v w
    ext i
    simp [projection_apply,mul_add,Finset.sum_add_distrib]
  map_smul' := by
    intro c v
    ext i
    simp [projection_apply,Finset.mul_sum,mul_left_comm]

def operator {rows cols : ℕ} (ω : Sample rows cols) : Space cols →L[ℝ] Space rows :=
  (linear ω).toContinuousLinearMap

theorem operator_apply {rows cols : ℕ} (ω : Sample rows cols) (v : Space cols) :
    operator ω v=projection v ω := rfl

theorem tensor_norm {rows cols : ℕ} (x : Space rows) (v : Space cols) :
    ‖tensor x v‖=‖x‖*‖v‖ := by
  have hh := tensor_inner x x v v
  simp only [real_inner_self_eq_norm_sq] at hh
  nlinarith [norm_nonneg (tensor x v),norm_nonneg x,norm_nonneg v,
    mul_nonneg (norm_nonneg x) (norm_nonneg v)]

/-- Frobenius domination for the actual row-by-column action. -/
theorem apply_norm_le {rows cols : ℕ} (ω : Sample rows cols) (v : Space cols) :
    ‖operator ω v‖ ≤ ‖ω‖*‖v‖ := by
  have hi := real_inner_le_norm (tensor (projection v ω) v) ω
  rw [← projection_inner v ω (projection v ω),real_inner_self_eq_norm_sq,tensor_norm] at hi
  change ‖projection v ω‖ ≤ ‖ω‖*‖v‖
  by_cases hz : ‖projection v ω‖=0
  · rw [hz]
    positivity
  · have hp : 0 < ‖projection v ω‖ := (norm_nonneg _).lt_of_ne' hz
    nlinarith

theorem operator_norm_le {rows cols : ℕ} (ω : Sample rows cols) : ‖operator ω‖ ≤ ‖ω‖ :=
  (operator ω).opNorm_le_bound (norm_nonneg _) (apply_norm_le ω)

def operatorLinear (rows cols : ℕ) :
    Sample rows cols →ₗ[ℝ] (Space cols →L[ℝ] Space rows) where
  toFun := operator
  map_add' := by
    intro x y
    ext v
    simp only [add_apply,operator_apply,map_add]
  map_smul' := by
    intro c x
    ext v
    simp only [smul_apply,operator_apply,map_smul,RingHom.id_apply]

def operatorMap (rows cols : ℕ) :
    Sample rows cols →L[ℝ] (Space cols →L[ℝ] Space rows) :=
  (operatorLinear rows cols).toContinuousLinearMap

theorem operator_measurable (rows cols : ℕ) : Measurable (operator (rows:=rows) (cols:=cols)) :=
  (operatorMap rows cols).measurable

end
end KakeyaFormal.GaussianLinearOperator
