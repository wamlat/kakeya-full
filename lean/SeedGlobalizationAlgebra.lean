import LocalizedSeedApplication
import FiniteLocalizedFamily

/-! Exact radius-to-density powers in the two-ends globalization. -/
namespace KakeyaFormal.SeedGlobalizationAlgebra
noncomputable section

/-- The precise density exponent induced by localization. -/
def densityPower (d alpha : ℝ) : ℝ := d/(1-alpha)
def radiusPower (d alpha : ℝ) : ℝ := (d-2+2*alpha)/(1-alpha)

theorem radiusPower_nonneg {d alpha : ℝ} (hd : 2 ≤ d) (ha : 0 ≤ alpha) (ha1 : alpha < 1) :
    0 ≤ radiusPower d alpha := div_nonneg (by linarith) (by linarith)

theorem densityPower_identity {d alpha : ℝ} (ha1 : alpha < 1) :
    2+radiusPower d alpha = densityPower d alpha := by
  have hn : 1-alpha ≠ 0 := ne_of_gt (by linarith)
  unfold radiusPower densityPower
  field_simp
  ring

/-- The geometric radius-density inequality supplies exactly the claimed
power of original shading density, with a fixed positive constant. -/
theorem radius_to_density {lam C rho d alpha : ℝ}
    (hlam : 0 < lam) (hC : 0 < C) (hrho : 0 < rho)
    (hd : 2 ≤ d) (ha : 0 ≤ alpha) (ha1 : alpha < 1)
    (hradius : lam ≤ C*rho^(1-alpha)) :
    C^(-radiusPower d alpha)*lam^(densityPower d alpha) ≤ lam^2*rho^(d-2+2*alpha) := by
  have hdens : lam/C ≤ rho^(1-alpha) := (div_le_iff₀ hC).mpr (by simpa only [mul_comm] using hradius)
  have hp := Real.rpow_le_rpow (div_pos hlam hC).le hdens (radiusPower_nonneg hd ha ha1)
  have hpow : (rho^(1-alpha))^(radiusPower d alpha) = rho^(d-2+2*alpha) := by
    rw [← Real.rpow_mul hrho.le]
    congr 1
    unfold radiusPower
    field_simp [ne_of_gt (by linarith : (0:ℝ) < 1-alpha)]
  rw [hpow,Real.div_rpow hlam.le hC.le] at hp
  have hh := mul_le_mul_of_nonneg_left hp (sq_nonneg lam)
  calc
    _ = lam^2*(lam^(radiusPower d alpha)/C^(radiusPower d alpha)) := by
      rw [← densityPower_identity ha1,Real.rpow_add hlam,Real.rpow_two,Real.rpow_neg hC.le]
      ring
    _ ≤ _ := hh

/-- A retained original-mass fraction upgrades the radius-density bound to
the actual common localized shading density. -/
theorem localized_density_lower {lam s C rho d alpha : ℝ}
    (hlam : 0 < lam) (hC : 0 < C) (hrho : 0 < rho)
    (hd : 2 ≤ d) (ha : 0 ≤ alpha) (ha1 : alpha < 1)
    (hradius : lam ≤ C*rho^(1-alpha)) (hret : rho^alpha*lam ≤ s) :
    C^(-radiusPower d alpha)*lam^(densityPower d alpha) ≤ s^2*rho^(d-2) := by
  have hh := pow_le_pow_left₀ (mul_pos (Real.rpow_pos_of_pos hrho alpha) hlam).le hret 2
  have hp := mul_le_mul_of_nonneg_right hh (Real.rpow_pos_of_pos hrho (d-2)).le
  have hid : (rho^alpha*lam)^2*rho^(d-2) = lam^2*rho^(d-2+2*alpha) := by
    rw [mul_pow,← Real.rpow_natCast,← Real.rpow_mul hrho.le]
    norm_num only [Nat.cast_ofNat]
    rw [mul_comm (rho^(alpha*(2:ℝ))) (lam^2),mul_assoc,← Real.rpow_add hrho]
    congr 2
    ring
  rw [hid] at hp
  exact (radius_to_density hlam hC hrho hd ha ha1 hradius).trans hp

/-- Choosing alpha from a prescribed density error gives that error exactly. -/
theorem choose_alpha {d eta : ℝ} (hd : 0 < d) (heta : 0 < eta) :
    0 < eta/(d+eta) ∧ eta/(d+eta) < 1 ∧ densityPower d (eta/(d+eta)) = d+eta := by
  refine ⟨div_pos heta (add_pos hd heta),(div_lt_one (add_pos hd heta)).mpr (by linarith),?_⟩
  unfold densityPower
  field_simp [hd.ne']
  ring

end
end KakeyaFormal.SeedGlobalizationAlgebra
