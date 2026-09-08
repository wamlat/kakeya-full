import OriginalPivotSlabs
import PivotFourthPower
import SelectedOutputDensity

/-! Original-parameter output, density and actual spatial-cutoff substitution
on one constructed pivot package. No original comparison count is replaced by
the number of recovered tubes. -/
namespace KakeyaFormal.OriginalPivotScalar
open Finset OriginalPivotSlabs PivotSelectionBudgets PivotOutputLowerBound
open ClosingEnergyAlgebra PivotFourthPower
noncomputable section
open Classical

def coefficient (k : ℕ) (width K cBase cClose p q eps : ℝ) : ℝ :=
  (cClose*(outputCoefficient k width/65536)*
    (SelectedOutputDensity.lowerCoefficient (k+1) width)^(q+eps)*
    (1/(2048*LegalSampleOutputs.outputConstant (k+2) width))^(q+eps-2)) /
      ((K+1/cBase)*(100:ℝ)^(p+1))

theorem coefficient_pos (k : ℕ) {width K cBase cClose p q eps : ℝ}
    (hw : 0 ≤ width) (hK : 0 < K) (hBase : 0 < cBase) (hClose : 0 < cClose) :
    0 < coefficient k width K cBase cClose p q eps := by
  have hQ := outputCoefficient_pos k hw
  have hR := SelectedOutputDensity.lowerCoefficient_pos (k+1) hw
  have hS := LegalSampleOutputs.outputConstant_pos (k+2) hw
  dsimp [coefficient]
  positivity

variable {k M : ℕ} {F : TubeFamily (k+2) M} {E : Finset (Cell (k+2))}
    {marks : Fin M → Finset (Cell (k+2))}
    {K δ A lam xi B theta width baseRadius m d p eps alpha : ℝ}
    (U : Package F E marks K δ A lam xi B theta width baseRadius m d p eps alpha)

/-- The actual pruning depth is bounded by the same positive base-two log
already present in the exact selected-output estimate. -/
theorem depth_log : (U.depth:ℝ)+1 ≤ pivotLog δ := by
  have hδ := U.scale_pos
  have hlog2 : 0 < Real.log (2:ℝ) := Real.log_pos (by norm_num)
  have hlog := Real.log_le_log (by positivity : (0:ℝ) < 1/δ)
    (div_le_div_of_nonneg_right (by norm_num : (1:ℝ) ≤ 2) hδ.le)
  have hh := div_le_div_of_nonneg_right hlog hlog2.le
  have hj := U.depth_bound
  unfold pivotLog Real.logb
  linarith

/-- The complete fourth-power substitution from the package's original
sigma/output data and the actual closing-energy consequence. The numerical
closing input is supplied by OriginalPivotEnergy on this same package. -/
theorem fourth_power {d' q cBase cClose rho : ℝ}
    (hK : 0 < K) (hBase : 0 < cBase) (hClose : 0 < cClose)
    (hA : 0 < A) (hlam : 0 < lam) (hxi : 0 < xi) (hxi1 : xi ≤ 1) (hM : 0 < M)
    (hp : 1 ≤ p) (hq : 2 ≤ q) (heps : 0 ≤ eps) (heps1 : eps ≤ 1)
    (hbase : cBase*A⁻¹*δ^(m-d+eps)*lam^p*(M:ℝ) ≤ (E.card:ℝ))
    (hrho : SelectedOutputDensity.lowerCoefficient (k+1) width*
      (kappa width B theta alpha)^6*(((2^U.selection.level:ℕ):ℝ)*δ) ≤ rho)
    (hclose : cClose*(kappa width B theta alpha)^5*
      (cutoff K E δ A lam xi m d p eps M U.depth)⁻¹*rho^(q+eps)*
      δ^(d-d'+1+eps)*(AngleFiberSelection.outputSupport U.selection.retained).card ≤ (E.card:ℝ)^2) :
    coefficient k width K cBase cClose p q eps*(kappa width B theta alpha)^(5*((k+1:ℕ):ℝ)+6*q+12)*
      A⁻¹*xi^(p+3)*(pivotLog δ)^(-(p+4))*δ^(-2*m-3-d'+3*eps)*
      lam^(p+2*q+4+2*eps)*((M:ℝ)*δ^m)^3 ≤ (E.card:ℝ)^4 := by
  have hδ := U.scale_pos
  have hδ1 := U.geometry.original_scale_le_one
  have hk := U.kappa_pos
  have hk1 := U.kappa_le_one
  have hE := U.recovered.comparison_pos
  have hMp : (0:ℝ) < (M:ℝ) := by exact_mod_cast hM
  have hL : 0 < pivotLog δ := zero_lt_one.trans_le (pivotLog_ge_one hδ hδ1)
  have hcut : 0 < cutoff K E δ A lam xi m d p eps M U.depth :=
    zero_lt_one.trans_le (le_max_left _ _)
  let sigma := ((2^U.selection.level:ℕ):ℝ)*δ
  let angles := xi^2*lam^2*(M:ℝ)^2/(δ^2*(E.card:ℝ))
  let cQ := outputCoefficient k width/65536
  let cR := SelectedOutputDensity.lowerCoefficient (k+1) width
  let cS := 1/(2048*LegalSampleOutputs.outputConstant (k+2) width)
  have hcQ : 0 < cQ := div_pos (outputCoefficient_pos k U.width_nonneg) (by norm_num)
  have hcR : 0 < cR := SelectedOutputDensity.lowerCoefficient_pos (k+1) U.width_nonneg
  have hcS : 0 < cS := by
    have hh := LegalSampleOutputs.outputConstant_pos (k+2) U.width_nonneg
    dsimp [cS]
    positivity
  have hSigma : cS*lam^(2:ℝ) ≤ sigma := by
    calc
      _ = lam^2/(2048*LegalSampleOutputs.outputConstant (k+2) width) := by
        rw [Real.rpow_ofNat]
        dsimp [cS]
        ring
      _ ≤ sigma := U.sigma_lower.le
  have hSigmaPos : 0 < sigma := (by positivity : 0 < cS*lam^(2:ℝ)).trans_le hSigma
  have hRhoPos : 0 < rho := (by positivity : 0 < cR*(kappa width B theta alpha)^6*sigma).trans_le hrho
  have hOutput : cQ*(kappa width B theta alpha)^(5*(k+1))*lam^6*angles/
      (sigma^2*δ^2*(pivotLog δ)^3) ≤ (AngleFiberSelection.outputSupport U.selection.retained).card := by
    convert U.output_lower using 1
    dsimp [cQ,angles,sigma]
    field_simp
  have hClosing : cClose*(kappa width B theta alpha)^6*
      (cutoff K E δ A lam xi m d p eps M U.depth)⁻¹*rho^(q+eps)*
      δ^(d-d'+1+eps)*(AngleFiberSelection.outputSupport U.selection.retained).card ≤ (E.card:ℝ)^2 := by
    have hpow : (kappa width B theta alpha)^6 ≤ (kappa width B theta alpha)^5 :=
      pow_le_pow_of_le_one hk.le hk1 (by omega : 5 ≤ (6:ℕ))
    refine le_trans ?_ hclose
    gcongr
  have hcombined := source_density_combination (k+1) hlam hδ hk hcut hL
    (by positivity : 0 ≤ angles) hClose hcQ hcR hcS hq heps hSigma hrho hOutput hClosing
  have hcutUpper := actual_cutoff_upper U.depth hK.le hBase hE hA hMp hδ hδ1 hlam hxi hxi1
    hp heps (depth_log U) hbase
  let CF := (K+1/cBase)*(100:ℝ)^(p+1)
  have hCF : 0 < CF := by dsimp [CF]; positivity
  have hangle : (1:ℝ)*xi^2*lam^2*(M:ℝ)^2/(δ^2*(E.card:ℝ)) ≤ angles := by
    dsimp [angles]
    simp only [one_mul,le_refl]
  have hcComb : 0 < cClose*cQ*cR^(q+eps)*cS^(q+eps-2) := by positivity
  have hh := source_fourth_power_density (k+1) hE hcut hA hδ hxi hlam hMp hL hk hk1 heps1
    hcComb (by norm_num : (0:ℝ) < 1) hCF rfl hcutUpper hangle hcombined
  convert hh using 1
  dsimp [coefficient,CF,cQ,cR,cS]
  ring

end
end KakeyaFormal.OriginalPivotScalar
