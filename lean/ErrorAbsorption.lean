import Configurations
import LogLoss

/-! Removal of simultaneous small scale errors, small density errors, and fixed
logarithmic losses for the actual geometric configuration estimates. Nonempty
integer shadings provide the density lower bound; empty families are handled
separately. This does not assume a density lower bound for arbitrary measurable
shadings, where it would be false. -/

namespace KakeyaFormal

theorem density_log_product {δ lam eta P ell : ℝ}
    (hd : 0 < δ) (hl : 0 < lam) (heta : 0 ≤ eta) (hell : 0 ≤ ell)
    (hdensity : δ/2 ≤ lam)
    (hlog : ell * δ^eta ≤ (Real.log (2/δ))^(-P)) :
    (ell * (2 : ℝ)^(-eta)) * δ^(2*eta) ≤
      lam^eta * (Real.log (2/δ))^(-P) := by
  have hdens := Real.rpow_le_rpow (div_nonneg hd.le (by norm_num)) hdensity heta
  have hprod := mul_le_mul hdens hlog (mul_nonneg hell (Real.rpow_nonneg hd.le _))
    (Real.rpow_nonneg hl.le _)
  have hid : (δ/2)^eta * (ell*δ^eta) = (ell*(2:ℝ)^(-eta))*δ^(2*eta) := by
    rw [Real.div_rpow hd.le (by norm_num), Real.rpow_neg (by norm_num : (0:ℝ) ≤ 2)]
    have hδ : δ^(2*eta) = δ^eta*δ^eta := by
      rw [show 2*eta=eta+eta by ring, Real.rpow_add hd]
    rw [hδ]
    ring
  rwa [hid] at hprod

def PerturbedDiscreteEstimate (k : ℕ) (m d p : ℝ) : Prop :=
  ∀ geom : Normalization, ∀ eta : ℝ, 0 < eta →
    ∃ P : ℝ, 0 ≤ P ∧ ∃ c : ℝ, 0 < c ∧
      ∀ F : ShadedConfiguration k geom m,
        c * F.A⁻¹ * F.δ^(m-d+eta) * F.lam^(p+eta) *
          (Real.log (2/F.δ))^(-P) * F.M ≤ (F.family.unionCells.card : ℝ)

theorem PerturbedDiscreteEstimate.remove_errors {k : ℕ} {m d p : ℝ}
    (h : PerturbedDiscreteEstimate k m d p) : DiscreteEstimate k m d p := by
  intro geom eps heps
  let eta := eps/3
  have heta : 0 < eta := by dsimp [eta]; linarith
  obtain ⟨P,hP,c,hc,hbound⟩ := h geom eta heta
  obtain ⟨ell,hell,hlogbound⟩ := inverse_log_power_uniform_bound hP heta
  refine ⟨c*ell*(2:ℝ)^(-eta), mul_pos (mul_pos hc hell) (Real.rpow_pos_of_pos (by norm_num) _), ?_⟩
  intro F
  by_cases hM : 0 < F.M
  · have hN : 1 ≤ F.δ⁻¹ := by
      have hh : (1 : ℝ) ≤ 1 / F.δ := (le_div_iff₀ F.scale_pos).mpr
        (by simpa only [one_mul] using F.scale_le_one)
      simpa only [one_div] using hh
    have hlog := hlogbound F.δ⁻¹ hN
    rw [Real.inv_rpow F.scale_pos.le, Real.rpow_neg F.scale_pos.le, inv_inv] at hlog
    simp only [← div_eq_mul_inv] at hlog
    have hprod := density_log_product F.scale_pos F.density_pos heta.le hell.le
      (F.density_ge_half_scale hM) hlog
    have hA : 0 ≤ F.A⁻¹ := inv_nonneg.mpr (by linarith [F.cap_ge_one])
    have hcoef : 0 ≤ c*F.A⁻¹*F.δ^(m-d+eta)*F.lam^p := by
      exact mul_nonneg (mul_nonneg (mul_nonneg hc.le hA)
        (Real.rpow_nonneg F.scale_pos.le _)) (Real.rpow_nonneg F.density_pos.le _)
    have hscaled := mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_left hprod hcoef) (Nat.cast_nonneg F.M)
    have hidδ : F.δ^(m-d+eps) = F.δ^(m-d+eta)*F.δ^(2*eta) := by
      rw [← Real.rpow_add F.scale_pos]
      congr 1
      dsimp [eta]
      ring
    have hidlam : F.lam^(p+eta) = F.lam^p*F.lam^eta := Real.rpow_add F.density_pos _ _
    have hfinal : (c*ell*(2:ℝ)^(-eta))*F.A⁻¹*F.δ^(m-d+eps)*F.lam^p*F.M ≤
        c*F.A⁻¹*F.δ^(m-d+eta)*F.lam^(p+eta)*(Real.log (2/F.δ))^(-P)*F.M := by
      rw [hidδ,hidlam]
      simpa only [mul_assoc, mul_left_comm, mul_comm] using hscaled
    exact hfinal.trans (hbound F)
  · have hzero : F.M = 0 := by omega
    simp only [hzero,Nat.cast_zero,mul_zero]
    exact Nat.cast_nonneg _

end KakeyaFormal
