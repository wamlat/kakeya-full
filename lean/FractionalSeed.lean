import CoveredSeed
import SeedCoverNormalization
import ErrorAbsorption

/-! The actual unrestricted fractional hairbrush seed. All localization,
coarse direction selection, common rescaling, angular groups, measurable
hairbrush, and loss absorption are constructed in imported verified modules. -/
namespace KakeyaFormal.FractionalSeed
open CoveredSeed SeedGlobalizationAlgebra AngularSeedEstimate AngularSeedLogLoss
open LocalizedGridTubes SeedCoverNormalization
noncomputable section

/-- Integer-shading density and the actual seed logarithm pay for the two
small exponent errors, with a constant fixed before both density and scale. -/
theorem density_seed_log_product {δ lam eta ell L : ℝ}
    (hδ : 0 < δ) (hlam : 0 < lam) (_hL : 0 < L) (heta : 0 ≤ eta) (hell : 0 ≤ ell)
    (hdensity : δ/2 ≤ lam) (hlog : ell*δ^eta ≤ L^(-(2:ℝ))) :
    (ell*(2:ℝ)^(-eta))*δ^(2*eta) ≤ lam^eta*L^(-(2:ℝ)) := by
  have hdens := Real.rpow_le_rpow (div_nonneg hδ.le (by norm_num)) hdensity heta
  have hprod := mul_le_mul hdens hlog (mul_nonneg hell (Real.rpow_nonneg hδ.le _))
    (Real.rpow_nonneg hlam.le _)
  have hid : (δ/2)^eta*(ell*δ^eta) = (ell*(2:ℝ)^(-eta))*δ^(2*eta) := by
    rw [Real.div_rpow hδ.le (by norm_num),Real.rpow_neg (by norm_num : (0:ℝ) ≤ 2)]
    rw [show 2*eta = eta+eta by ring,Real.rpow_add hδ]
    ring
  rwa [hid] at hprod

/-- Both scale and density homothety factors combine into one fixed power. -/
theorem cover_power_identity {δ lam C m d eps : ℝ}
    (hδ : 0 < δ) (hlam : 0 < lam) (hC : 0 < C) :
    C^(-(m+eps))*δ^(m-d+eps)*lam^d = (δ/C)^(m-d+eps)*(lam/C)^d := by
  have hpow : C^(m+eps) = C^(m-d+eps)*C^d := by
    rw [← Real.rpow_add hC]
    congr 1
    ring
  rw [Real.div_rpow hδ.le hC.le,Real.div_rpow hlam.le hC.le,Real.rpow_neg hC.le,hpow]
  simp only [mul_inv_rev]
  ring

/-- Fully quantified actual fractional seed in every ambient dimension at
least two. Its constant is fixed before every actual geometric configuration. -/
theorem fractional_discrete_seed (k : ℕ) {m : ℝ} (hm : 3 < m) :
    DiscreteEstimate (k+2) m ((m+3)/2) ((m+3)/2) := by
  intro geom eps heps
  let d := (m+3)/2
  let eta := eps/3
  let alpha := eta/(d+eta)
  let beta := (m-1)/4
  let C := coverFactor geom.width
  have hd : 0 < d := by dsimp [d]; linarith
  have heta : 0 < eta := by dsimp [eta]; positivity
  obtain ⟨halpha,halpha1,hpower⟩ := choose_alpha hd heta
  have hbeta : 0 < beta := by dsimp [beta]; linarith
  have hbetaS : beta ≤ (m-1)/2 := by dsimp [beta]; linarith
  have hC : 0 < C := coverFactor_pos geom.width
  obtain ⟨c,hc,hcovered⟩ := covered_seed k (width := localWidth geom.width) halpha halpha1
    hbeta hbetaS (by linarith : 1 ≤ m) heta
  obtain ⟨ell,hell,hlog⟩ := seedLog_absorption (by norm_num : (0:ℝ) ≤ 2) heta
  let c₀ := c*ell*(2:ℝ)^(-eta)
  have hc₀ : 0 < c₀ := by dsimp [c₀]; positivity
  refine ⟨c₀/C^(m+eps),by positivity,?_⟩
  intro F
  by_cases hM : 0 < F.M
  · let G := SeedCoverNormalization.family F.family F.δ geom.width
    let δ₀ := F.δ/C
    let lam₀ := F.lam/C
    have hδ₀ : 0 < δ₀ := div_pos F.scale_pos hC
    have hδ₀1 : δ₀ ≤ 1 := (normalized_scale F.scale_pos F.scale_le_one).2
    have hlam₀ : 0 < lam₀ := div_pos F.density_pos hC
    have hcap : G.CapBound δ₀ m F.A := family_cap_bound F.family F.scale_pos F.scale_le_one
      (by linarith : 0 ≤ m) (zero_le_one.trans F.cap_ge_one) F.cap_bound
    have hcoveredF := hcovered F.M G δ₀ lam₀ F.A hM hδ₀ hδ₀1 hlam₀ F.cap_ge_one
      (family_admissible F.family F.scale_pos F.admissible) (family_comparable F.family F.comparable) hcap
      (fun i => (G.tube i).base) (family_cover F.family F.scale_pos F.scale_le_one F.admissible)
    change c*F.A⁻¹*δ₀^((m-3)/2+eta)*lam₀^(densityPower d alpha)*
      (seedLog δ₀)^(-(2:ℝ))*(F.M:ℝ) ≤ (G.unionCells.card:ℝ) at hcoveredF
    rw [hpower,family_union_card] at hcoveredF
    have hdens : δ₀/2 ≤ lam₀ := by
      have hh := div_le_div_of_nonneg_right (F.density_ge_half_scale hM) hC.le
      dsimp [δ₀,lam₀]
      convert hh using 1 <;> first | rfl | ring
    have hL : 0 < seedLog δ₀ := zero_lt_one.trans_le (seedLog_ge_one hδ₀ hδ₀1)
    have hprod := density_seed_log_product hδ₀ hlam₀ hL heta.le hell.le hdens (hlog δ₀ hδ₀ hδ₀1)
    have hfac : 0 ≤ c*F.A⁻¹*δ₀^((m-3)/2+eta)*lam₀^d*(F.M:ℝ) := by
      have hA := zero_lt_one.trans_le F.cap_ge_one
      positivity
    have hscaled := mul_le_mul_of_nonneg_left hprod hfac
    have hnorm : c₀*F.A⁻¹*δ₀^(m-d+eps)*lam₀^d*(F.M:ℝ) ≤ (F.family.unionCells.card:ℝ) := by
      have hexp : m-d+eps = ((m-3)/2+eta)+2*eta := by dsimp [d,eta]; ring
      calc
        _ = (c*F.A⁻¹*δ₀^((m-3)/2+eta)*lam₀^d*(F.M:ℝ))*
            ((ell*(2:ℝ)^(-eta))*δ₀^(2*eta)) := by
          rw [hexp,Real.rpow_add hδ₀]
          dsimp [c₀]
          ring
        _ ≤ _ := hscaled
        _ = c*F.A⁻¹*δ₀^((m-3)/2+eta)*lam₀^(d+eta)*(seedLog δ₀)^(-(2:ℝ))*(F.M:ℝ) := by
          rw [Real.rpow_add hlam₀]
          ring
        _ ≤ _ := hcoveredF
    calc
      _ = c₀*F.A⁻¹*(C^(-(m+eps))*F.δ^(m-d+eps)*F.lam^d)*(F.M:ℝ) := by
        rw [Real.rpow_neg hC.le]
        dsimp only [d]
        ring
      _ = c₀*F.A⁻¹*((F.δ/C)^(m-d+eps)*(F.lam/C)^d)*(F.M:ℝ) := by
        rw [cover_power_identity F.scale_pos F.density_pos hC]
      _ = c₀*F.A⁻¹*δ₀^(m-d+eps)*lam₀^d*(F.M:ℝ) := by dsimp [δ₀,lam₀]; ring
      _ ≤ _ := hnorm
  · have hz : F.M = 0 := by omega
    simp only [hz,Nat.cast_zero,mul_zero]
    exact Nat.cast_nonneg _

/-- The precise actual real-cap seed required by the existing endpoint
iteration. No fractional seed, two-ends reduction, or analytic bound is assumed. -/
theorem fractional_real_cap_seed {m : ℝ} (hm : 3 < m) :
    RealCapEstimate m ((m+3)/2) ((m+3)/2) := by
  intro dimension hdim
  cases dimension with
  | zero => norm_num at hdim; linarith
  | succ n =>
      cases n with
      | zero => norm_num at hdim; linarith
      | succ k => exact fractional_discrete_seed k hm

end
end KakeyaFormal.FractionalSeed
