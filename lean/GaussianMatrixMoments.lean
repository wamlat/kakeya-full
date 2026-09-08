import GaussianLinearOperator

/-! Actual second moments and an operator-norm tail for the original matrix.
The moment is derived from standard Gaussian coordinates, not assumed. -/
namespace KakeyaFormal.GaussianMatrixMoments
open MeasureTheory ProbabilityTheory GaussianMatrix GaussianLinearOperator
open scoped RealInnerProductSpace
noncomputable section

section General
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]

theorem norm_sq_integrable : Integrable (fun x : E => ‖x‖^2) (stdGaussian E) := by
  exact (IsGaussian.memLp_two_id (μ:=stdGaussian E)).integrable_norm_pow' (p:=2)

/-- The standard Gaussian second moment equals the actual real dimension. -/
theorem stdGaussian_norm_sq : (∫ x : E, ‖x‖^2 ∂stdGaussian E) = Module.finrank ℝ E := by
  let b := stdOrthonormalBasis ℝ E
  have hint (i : Fin (Module.finrank ℝ E)) :
      Integrable (fun x : E => ⟪b i,x⟫^2) (stdGaussian E) := by
    have hh0 : MemLp (fun x : E => ⟪b i,x⟫) 2 (stdGaussian E) :=
      (IsGaussian.memLp_two_id (μ:=stdGaussian E)).const_inner (b i)
    have hh := hh0.integrable_norm_pow' (p:=2)
    simpa only [Real.norm_eq_abs,sq_abs] using hh
  have hmean (i : Fin (Module.finrank ℝ E)) :
      (∫ x : E, ⟪b i,x⟫ ∂stdGaussian E)=0 := integral_strongDual_stdGaussian (innerSL ℝ (b i))
  have hmoment (i : Fin (Module.finrank ℝ E)) :
      (∫ x : E, ⟪b i,x⟫^2 ∂stdGaussian E)=1 := by
    have hh := variance_dual_stdGaussian (innerSL ℝ (b i))
    rw [variance_eq_integral (by fun_prop)] at hh
    change (∫ x : E, (⟪b i,x⟫-(∫ y : E, ⟪b i,y⟫ ∂stdGaussian E))^2 ∂stdGaussian E)=_ at hh
    simpa only [hmean i,sub_zero,innerSL_apply_norm,b.norm_eq_one,one_pow] using hh
  have heq (x : E) : ‖x‖^2=∑ i, ⟪b i,x⟫^2 := (b.sum_sq_inner_right x).symm
  simp_rw [heq]
  rw [integral_finsetSum Finset.univ (fun i _ => hint i)]
  simp only [hmoment,Finset.sum_const,Finset.card_univ,Fintype.card_fin,nsmul_eq_mul,mul_one]

end General

theorem matrix_norm_sq (rows cols : ℕ) :
    (∫ ω : Sample rows cols, ‖ω‖^2 ∂law rows cols)=(rows:ℝ)*cols := by
  rw [law,stdGaussian_norm_sq]
  simp [Sample,finrank_euclideanSpace]

/-- The actual operator-norm tail is bounded using its proved Frobenius
domination and the matrix's computed second moment. -/
theorem tail_bound (rows cols : ℕ) {K : ℝ} (hK : 0 < K) :
    (law rows cols).real {ω | K ≤ ‖operator ω‖} ≤ ((rows:ℝ)*cols)/K^2 := by
  have hm := mul_meas_ge_le_integral_of_nonneg
    (μ:=law rows cols) (f:=fun ω : Sample rows cols => ‖ω‖^2)
    (Filter.Eventually.of_forall (fun _ => sq_nonneg _))
    (norm_sq_integrable (E:=Sample rows cols)) (K^2)
  rw [matrix_norm_sq] at hm
  have hsub : {ω : Sample rows cols | K ≤ ‖operator ω‖} ⊆ {ω | K^2 ≤ ‖ω‖^2} := by
    intro ω hω
    exact (sq_le_sq₀ hK.le (norm_nonneg ω)).mpr (hω.trans (operator_norm_le ω))
  have hmeasure := measureReal_mono hsub (measure_ne_top (law rows cols) _)
  exact hmeasure.trans ((le_div_iff₀ (sq_pos_of_pos hK)).mpr (by simpa only [mul_comm] using hm))

theorem five_by_seven_tail :
    (law 5 7).real {ω | (20:ℝ) ≤ ‖operator ω‖} ≤ 7/80 := by
  have hh := tail_bound 5 7 (by norm_num : (0:ℝ)<20)
  norm_num at hh ⊢
  exact hh

end
end KakeyaFormal.GaussianMatrixMoments
