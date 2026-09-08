import GaussianProjectedSelection
import LogLoss

/-! Closing the original Gaussian projection route: the actual retained
population loses one logarithm, which is absorbed uniformly in delta. -/
namespace KakeyaFormal.GaussianProjectionAlgebra
noncomputable section

theorem inverse_log_delta {eta : ℝ} (heta : 0 < eta) :
    ∃ ell : ℝ, 0 < ell ∧ ∀ δ : ℝ, 0 < δ → δ ≤ 1 →
      ell*δ^eta ≤ (Real.log (2/δ))⁻¹ := by
  obtain ⟨ell,hell,hbound⟩ := inverse_log_power_uniform_bound
    (by norm_num : (0:ℝ) ≤ 1) heta
  refine ⟨ell,hell,?_⟩
  intro δ hδ hδ1
  have hh := hbound (1/δ) ((le_div_iff₀ hδ).mpr (by simpa using hδ1))
  have he : (1/δ)^(-eta)=δ^eta := by
    rw [one_div,← Real.rpow_neg_eq_inv_rpow,neg_neg]
  simpa only [he,mul_one_div,Real.rpow_neg_one] using hh

/-- The population factor and the target five-dimensional bound are
combined with exact powers. All zero populations are allowed. -/
theorem closing {δ lam A M M' E c t ell eta : ℝ}
    (hδ : 0 < δ) (hlam : 0 ≤ lam) (hA : 0 < A)
    (hM : 0 ≤ M) (hc : 0 ≤ c) (ht : 0 ≤ t)
    (hlog : 0 < Real.log (2/δ))
    (habsorb : ell*δ^eta ≤ (Real.log (2/δ))⁻¹)
    (hpop : t*M/(A*Real.log (2/δ)) ≤ M')
    (hseed : c*δ^((1:ℝ)/2+eta)*lam^((7:ℝ)/2)*M' ≤ E) :
    (c*t*ell)*A⁻¹*δ^((1:ℝ)/2+2*eta)*lam^((7:ℝ)/2)*M ≤ E := by
  have hf : 0 ≤ c*δ^((1:ℝ)/2+eta)*lam^((7:ℝ)/2) := by positivity
  have hpop' := mul_le_mul_of_nonneg_left hpop hf
  have habsorb' := mul_le_mul_of_nonneg_left habsorb
    (show 0 ≤ c*δ^((1:ℝ)/2+eta)*lam^((7:ℝ)/2)*t*M*A⁻¹ by positivity)
  have hexp : (1:ℝ)/2+2*eta=((1:ℝ)/2+eta)+eta := by ring
  calc
    _ = (c*δ^((1:ℝ)/2+eta)*lam^((7:ℝ)/2)*t*M*A⁻¹)*(ell*δ^eta) := by
      rw [hexp,Real.rpow_add hδ]
      ring
    _ ≤ (c*δ^((1:ℝ)/2+eta)*lam^((7:ℝ)/2)*t*M*A⁻¹)*(Real.log (2/δ))⁻¹ := habsorb'
    _ = (c*δ^((1:ℝ)/2+eta)*lam^((7:ℝ)/2))*(t*M/(A*Real.log (2/δ))) := by
      field_simp
    _ ≤ c*δ^((1:ℝ)/2+eta)*lam^((7:ℝ)/2)*M' := hpop'
    _ ≤ E := hseed

end
end KakeyaFormal.GaussianProjectionAlgebra
