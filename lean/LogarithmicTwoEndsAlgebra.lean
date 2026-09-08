import Mathlib

/-! The explicit logarithmic loss forced by an actual localization-radius
constraint. This is scalar algebra only; the radius and density hypotheses
must be derived from the original shadings by its geometric consumer. -/
namespace KakeyaFormal.LogarithmicTwoEndsAlgebra
noncomputable section

def lossPower (beta C D : ℝ) : ℝ := max 0 (beta*C+D-C)/beta

theorem lossPower_nonneg {beta C D : ℝ} (hbeta : 0 < beta) :
    0 ≤ lossPower beta C D := div_nonneg (le_max_left _ _) hbeta.le

/-- Raising the actual radius constraint uses a nonnegative power. No lower
bound on the radius by a separately chosen root is needed. -/
theorem constraint_power {a rho beta q : ℝ} (ha : 0 < a) (hrho : 0 < rho)
    (hq : 0 ≤ q) (hconstraint : 1 ≤ a*rho^beta) :
    a^(-q) ≤ rho^(beta*q) := by
  have h := Real.one_le_rpow hconstraint hq
  rw [Real.mul_rpow ha.le (Real.rpow_nonneg hrho.le _),
    ← Real.rpow_mul hrho.le] at h
  have hp : 0 < a^q := Real.rpow_pos_of_pos ha _
  rw [Real.rpow_neg ha.le, ← one_div]
  exact (div_le_iff₀ hp).mpr (by simpa only [mul_comm] using h)

/-- Preserve the density power C, paying only an explicit power of L. The
formula is valid even when the combined radius exponent is negative. The
exponent b may be any real number; later log budgets use b nonnegative. -/
theorem density_factor {beta C D rho lam s B0 L b : ℝ}
    (hbeta : 0 < beta) (hC : 0 ≤ C) (hrho : 0 < rho) (hrho1 : rho ≤ 1)
    (hlam : 0 < lam) (hB0 : 0 < B0) (hL : 0 < L)
    (hs : rho^beta*lam ≤ s)
    (hconstraint : 1 ≤ 2*(B0*L^b)*rho^beta) :
    (2*B0)^(-lossPower beta C D)*L^(-(b*lossPower beta C D))*lam^C ≤
      s^C*rho^(D-C) := by
  let q := lossPower beta C D
  have hq : 0 ≤ q := lossPower_nonneg hbeta
  have hqeq : beta*q = max 0 (beta*C+D-C) := by
    dsimp [q, lossPower]
    field_simp
  have hpower := constraint_power
    (show 0 < 2*(B0*L^b) by positivity) hrho hq hconstraint
  have hcoef : (2*(B0*L^b))^(-q) = (2*B0)^(-q)*L^(-(b*q)) := by
    rw [show 2*(B0*L^b) = (2*B0)*(L^b) by ring,
      Real.mul_rpow (by positivity) (Real.rpow_nonneg hL.le _),
      ← Real.rpow_mul hL.le]
    congr 2
    ring
  rw [hcoef, hqeq] at hpower
  have hscale : (2*B0)^(-q)*L^(-(b*q)) ≤ rho^(beta*C+D-C) :=
    hpower.trans (Real.rpow_le_rpow_of_exponent_ge hrho hrho1 (le_max_right _ _))
  have hdensity := Real.rpow_le_rpow (show 0 ≤ rho^beta*lam by positivity) hs hC
  calc
    _ ≤ rho^(beta*C+D-C)*lam^C :=
      mul_le_mul_of_nonneg_right hscale (Real.rpow_nonneg hlam.le _)
    _ = (rho^beta*lam)^C*rho^(D-C) := by
      rw [Real.mul_rpow (Real.rpow_nonneg hrho.le _) hlam.le,
        ← Real.rpow_mul hrho.le,
        show beta*C+D-C = beta*C+(D-C) by ring,
        Real.rpow_add hrho]
      ring
    _ ≤ s^C*rho^(D-C) :=
      mul_le_mul_of_nonneg_right hdensity (Real.rpow_nonneg hrho.le _)

end
end KakeyaFormal.LogarithmicTwoEndsAlgebra
