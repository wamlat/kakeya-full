import AdmissiblePivotClosing
import PivotLossAbsorption

/-! The original cutoff and fourth-power substitutions need only p>0. The
fixed natural-log comparison also holds throughout that full positive range. -/
namespace KakeyaFormal.PositivePivotAlgebra
open Finset AdmissiblePivotSlabs PivotSelectionBudgets PivotOutputLowerBound
open ClosingEnergyAlgebra PivotFourthPower PivotLossAbsorption
open OriginalPivotSlabs (cutoff)
open OriginalPivotScalar (coefficient)
open AdmissiblePivotClosing (depth_log)
noncomputable section
open Classical

/-- The exact max-cutoff proof uses positivity of p+1, not convexity. -/
theorem actual_cutoff_upper (J : ℕ)
    {E A M δ lam xi L K c m d p eps : ℝ}
    (hK : 0 ≤ K) (hc : 0 < c) (hE : 0 < E) (hA : 0 < A) (hM : 0 < M)
    (hδ : 0 < δ) (hδ1 : δ ≤ 1) (hlam : 0 < lam) (hxi : 0 < xi) (hxi1 : xi ≤ 1)
    (hp : 0 < p) (heps : 0 ≤ eps) (hJ : (J:ℝ)+1 ≤ L)
    (hbase : c*A⁻¹*δ^(m-d+eps)*lam^p*M ≤ E) :
    max 1 (K*E*A*δ^(d-m-eps)*(((xi/100)/((J:ℝ)+1))^(-(p+1)))*lam^(-p)/M) ≤
      ((K+1/c)*(100:ℝ)^(p+1))*E*A*δ^(d-m-2*eps)*xi^(-(p+1))*L^(p+1)*lam^(-p)/M := by
  let Y := E*A*δ^(d-m-eps)*lam^(-p)/M
  let eta := (xi/100)/((J:ℝ)+1)
  have hY : c ≤ Y := by
    have hh := inverse_base_bound hc hA hδ hlam hM hbase
    rw [show -(m-d+eps)=d-m-eps by ring] at hh
    exact hh
  have heta : 0 < eta := by dsimp [eta]; positivity
  have heta1 : eta ≤ 1 := by
    dsimp [eta]
    apply (div_le_iff₀ (by positivity : (0:ℝ) < (J:ℝ)+1)).mpr
    linarith [Nat.cast_nonneg (α := ℝ) J]
  have hh := max_cutoff_bound hK hc hY heta heta1 (by linarith : 0 ≤ p+1)
  have hid : K*E*A*δ^(d-m-eps)*eta^(-(p+1))*lam^(-p)/M = K*Y*eta^(-(p+1)) := by dsimp [Y]; ring
  change max 1 (K*E*A*δ^(d-m-eps)*eta^(-(p+1))*lam^(-p)/M) ≤ _
  rw [hid]
  refine hh.trans ?_
  have hd := Real.rpow_le_rpow_of_exponent_ge hδ hδ1
    (by linarith : d-m-2*eps ≤ d-m-eps)
  have hdepth := Real.rpow_le_rpow (by positivity : (0:ℝ) ≤ (J:ℝ)+1) hJ (by linarith : 0 ≤ p+1)
  have hpow : eta^(-(p+1)) = (100:ℝ)^(p+1)*xi^(-(p+1))*((J:ℝ)+1)^(p+1) :=
    marked_budget_power hxi J
  calc
    _ = ((K+1/c)*(100:ℝ)^(p+1)*E*A*xi^(-(p+1))*lam^(-p)/M)*
        δ^(d-m-eps)*((J:ℝ)+1)^(p+1) := by rw [hpow]; dsimp [Y]; ring
    _ ≤ ((K+1/c)*(100:ℝ)^(p+1)*E*A*xi^(-(p+1))*lam^(-p)/M)*
        δ^(d-m-2*eps)*L^(p+1) := by gcongr
    _ = _ := by ring


/-- Natural-log comparison uses only positivity of p+4. -/
theorem natural_log_fourth {δ c A kap xi p q n m d' e lam S E : ℝ}
    (hδ : 0 < δ) (hδ1 : δ ≤ 1) (hc : 0 < c) (hA : 0 < A)
    (hk : 0 < kap) (hx : 0 < xi) (hp : 0 < p) (hlam : 0 < lam) (hS : 0 ≤ S)
    (hfour : c*kap^(5*n+6*q+12)*A⁻¹*xi^(p+3)*
      (PivotSelectionBudgets.pivotLog δ)^(-(p+4))*δ^(-2*m-3-d'+3*e)*
      lam^(p+2*q+4+2*e)*S^3 ≤ E^4) :
    (c*(3/Real.log 2)^(-(p+4)))*A⁻¹*kap^(5*n+6*q+12)*xi^(p+3)*
      (Real.log (2/δ))^(-(p+4))*δ^(-2*m-3-d'+3*e)*
      lam^(p+2*q+4+2*e)*S^3 ≤ E^4 := by
  have hlog := pivotLog_inverse_power hδ hδ1 (by linarith : 0 ≤ p+4)
  have hh := mul_le_mul_of_nonneg_left hlog
    (by positivity : 0 ≤ c*kap^(5*n+6*q+12)*A⁻¹*xi^(p+3)*
      δ^(-2*m-3-d'+3*e)*lam^(p+2*q+4+2*e)*S^3)
  calc
    _ = (c*kap^(5*n+6*q+12)*A⁻¹*xi^(p+3)*δ^(-2*m-3-d'+3*e)*
        lam^(p+2*q+4+2*e)*S^3)*
        ((3/Real.log 2)^(-(p+4))*(Real.log (2/δ))^(-(p+4))) := by ring
    _ ≤ (c*kap^(5*n+6*q+12)*A⁻¹*xi^(p+3)*δ^(-2*m-3-d'+3*e)*
        lam^(p+2*q+4+2*e)*S^3)*(PivotSelectionBudgets.pivotLog δ)^(-(p+4)) := hh
    _ = _ := by ring
    _ ≤ _ := hfour


variable {k M : ℕ} {F : TubeFamily (k+2) M} {E : Finset (Cell (k+2))}
    {marks : Fin M → Finset (Cell (k+2))}
    {K δ A lam xi B theta width baseRadius m d p eps alpha kap : ℝ}
    (U : Package F E marks K δ A lam xi B theta width baseRadius m d p eps alpha kap)

/-- The complete fourth-power substitution from the package's original
sigma/output data and the actual closing-energy consequence. The numerical
closing input is supplied by `energy` on this same package. -/
theorem fourth_power {d' q cBase cClose rho : ℝ}
    (hK : 0 < K) (hBase : 0 < cBase) (hClose : 0 < cClose)
    (hA : 0 < A) (hlam : 0 < lam) (hxi : 0 < xi) (hxi1 : xi ≤ 1) (hM : 0 < M)
    (hp : 0 < p) (hq : 2 ≤ q) (heps : 0 ≤ eps) (heps1 : eps ≤ 1)
    (hbase : cBase*A⁻¹*δ^(m-d+eps)*lam^p*(M:ℝ) ≤ (E.card:ℝ))
    (hrho : SelectedOutputDensity.lowerCoefficient (k+1) width*
      kap^6*(((2^U.selection.level:ℕ):ℝ)*δ) ≤ rho)
    (hclose : cClose*kap^5*
      (cutoff K E δ A lam xi m d p eps M U.depth)⁻¹*rho^(q+eps)*
      δ^(d-d'+1+eps)*(AngleFiberSelection.outputSupport U.selection.retained).card ≤ (E.card:ℝ)^2) :
    coefficient k width K cBase cClose p q eps*kap^(5*((k+1:ℕ):ℝ)+6*q+12)*
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
  have hRhoPos : 0 < rho := (by positivity : 0 < cR*kap^6*sigma).trans_le hrho
  have hOutput : cQ*kap^(5*(k+1))*lam^6*angles/
      (sigma^2*δ^2*(pivotLog δ)^3) ≤ (AngleFiberSelection.outputSupport U.selection.retained).card := by
    convert U.output_lower using 1
    dsimp [cQ,angles,sigma]
    field_simp
  have hClosing : cClose*kap^6*
      (cutoff K E δ A lam xi m d p eps M U.depth)⁻¹*rho^(q+eps)*
      δ^(d-d'+1+eps)*(AngleFiberSelection.outputSupport U.selection.retained).card ≤ (E.card:ℝ)^2 := by
    have hpow : kap^6 ≤ kap^5 :=
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
end KakeyaFormal.PositivePivotAlgebra
