import AnisotropicSamplingRetention
import AnisotropicSamplingBudgets
import PivotLossAbsorption

/-! The actual measured selection preserves the required density power times
population. Its joint mass estimate avoids paying the population loss twice. -/
namespace KakeyaFormal.AnisotropicDensityPower
open AnisotropicSamplingBudgets AnisotropicSamplingRetention
noncomputable section

theorem power_mass {a b L x C lam lamNew M N : ℝ}
    (ha : 0 < a) (hb : 0 < b) (hL : 0 < L) (hC : 1 ≤ C)
    (hlam : 0 < lam) (hnew : 0 < lamNew) (hM : 0 ≤ M)
    (hdensity : a*L^(-x)*lam ≤ lamNew)
    (hmass : b*L^(-(x+1))*lam*M ≤ lamNew*N) :
    (a^(C-1)*b)*L^(-(x*C+1))*lam^C*M ≤ lamNew^C*N := by
  have hp := Real.rpow_le_rpow (by positivity : 0 ≤ a*L^(-x)*lam)
    hdensity (by linarith : 0 ≤ C-1)
  have hh := mul_le_mul hp hmass (by positivity : 0 ≤ b*L^(-(x+1))*lam*M)
    (Real.rpow_nonneg hnew.le (C-1))
  have hid : (a*L^(-x)*lam)^(C-1)*(b*L^(-(x+1))*lam*M) =
      (a^(C-1)*b)*L^(-(x*C+1))*lam^C*M := by
    rw [Real.mul_rpow (mul_pos ha (Real.rpow_pos_of_pos hL _)).le hlam.le,
      Real.mul_rpow ha.le (Real.rpow_pos_of_pos hL _).le,
      ← Real.rpow_mul hL.le]
    calc
      _ = (a^(C-1)*b)*(L^(-x*(C-1))*L^(-(x+1)))*
          (lam^(C-1)*lam)*M := by ring
      _ = _ := by
        rw [← Real.rpow_add hL,
          show lam^(C-1)*lam = lam^C by
            calc
              _ = lam^(C-1)*lam^(1:ℝ) := by rw [Real.rpow_one]
              _ = _ := by rw [← Real.rpow_add hlam]; congr 1; ring]
        rw [show -x*(C-1)+-(x+1) = -(x*C+1) by ring]
  rw [hid] at hh
  apply hh.trans_eq
  rw [show lamNew^(C-1)*(lamNew*N) = (lamNew^(C-1)*lamNew^(1:ℝ))*N by
    rw [Real.rpow_one]; ring,← Real.rpow_add hnew]
  rw [show C-1+1=C by ring]

/-- The literal selected output supplies both inputs to the power estimate;
there is no assumed population or weighted-mass retention premise. -/
theorem output_power {k M : ℕ} {Full : Fin M → Set (Space (k+1))}
    {u : Space (k+1)} {q : Cell k}
    {δ tau width R angular lam e B alpha beta K m A e₀ x L C : ℝ}
    (O : Output Full u q δ tau width R angular lam e B alpha beta K m A)
    (he₀ : 0 < e₀) (hx : 0 ≤ x) (hL : 1 ≤ L) (hC : 1 ≤ C)
    (he : e₀*L^(-x) ≤ e) :
    ((e₀/4)^(C-1)*(e₀/(16*depthCoefficient e₀ x)))*
      L^(-(x*C+1))*lam^C*(M:ℝ) ≤ O.density^C*(O.N:ℝ) := by
  have hLp : 0 < L := zero_lt_one.trans_le hL
  have hlam : 0 < lam := O.input.density_pos.trans_le O.density_upper
  have hd := depth_bound he₀ hx hL O.effective_pos he O.depth_bound
  exact power_mass (by positivity) (by have := depthCoefficient_pos (e₀:=e₀) hx; positivity)
    hLp hC hlam O.input.density_pos (Nat.cast_nonneg M)
    (density_retention hlam.le he O.density_lower)
    (density_population_retention he₀ hx hLp hlam.le (Nat.cast_nonneg M) he hd
      O.density_population_lower)

end
end KakeyaFormal.AnisotropicDensityPower
