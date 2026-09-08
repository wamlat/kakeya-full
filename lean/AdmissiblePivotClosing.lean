import AdmissiblePivotSlabs
import OriginalPivotEnergy
import OriginalPivotScalar

/-! Actual lifted closing and original fourth-power substitution for any
constructed admissible-radius package. All radius dependence is displayed;
no product formula or conditioning budget is used. -/
namespace KakeyaFormal.AdmissiblePivotClosing
open Finset ActualLabelSelection AngleFiberSelection
open AdmissiblePivotSlabs SelectedBaseFamilies SelectedColoredFamilies
open OriginalPivotSlabs (cutoff)
open OriginalPivotEnergy (geometricFactor geometricFactor_pos cap_factorization)
open OriginalPivotScalar (coefficient)
open PivotSelectionBudgets PivotOutputLowerBound ClosingEnergyAlgebra PivotFourthPower
open scoped BigOperators
noncomputable section
open Classical

/-- Actual normalized lifted closing, with its fixed geometric factor absorbed
before every original configuration and every admissible radius. -/
theorem energy {k : ℕ} {d d' r eps : ℝ}
    (width baseRadius : ℝ) (hw : 0 ≤ width) (hd : 0 ≤ d)
    (hlift : DiscreteEstimate (k+3) d d' r) (hr : 1 ≤ r) (heps : 0 < eps) :
    ∃ c : ℝ, 0 < c ∧ ∀ (K : ℝ) {M : ℕ}
      (F : TubeFamily (k+2) M) (E : Finset (Cell (k+2)))
      (marks : Fin M → Finset (Cell (k+2)))
      {δ A lam xi B theta m p alpha kap : ℝ}
      (U : Package F E marks K δ A lam xi B theta width baseRadius m d p eps alpha kap),
      ∃ rho : ℝ, 0 < rho ∧
        SelectedOutputDensity.lowerCoefficient (k+1) width*kap^6*
          (((2^U.selection.level:ℕ):ℝ)*δ) ≤ rho ∧
        c*kap^5*(cutoff K E δ A lam xi m d p eps M U.depth)⁻¹*
          rho^r*δ^(d-d'+1+eps)*(outputSupport U.selection.retained).card ≤ (E.card : ℝ)^2 := by
  obtain ⟨c₀,hc₀,hclose⟩ := ConstructedPivotClosing.construct
    (k:=k+1) (R:=baseRadius) hw hd hlift hr heps
  let c := c₀/geometricFactor k width baseRadius d
  have hc : 0 < c := div_pos hc₀ (geometricFactor_pos k hw hd)
  refine ⟨c,hc,?_⟩
  intro K M F E marks δ A lam xi B theta m p alpha kap U
  let L := cutoff K E δ A lam xi m d p eps M U.depth
  let Cball := PrunedGraphLift.spatialConstant (k+2) width baseRadius d*L
  obtain ⟨families,hrho,hlower,henergy⟩ := hclose
    U.kappa_pos U.recovered.admissible U.selection U.lines Cball U.scale_pos
    U.geometry.original_scale_le_one U.kappa_le_one U.normalized_coefficient_ge_one
    U.recovered.bounded U.normalized_spatial U.geometry.attached_witness_small
  let rho := SelectedOutputDensity.rho U.selection U.lines (color U.selection)
    (shading U.selection U.lines families)
  have hcard : (U.recovered.family.unionCells.card : ℝ) ≤ (E.card : ℝ) := by
    exact_mod_cast card_le_card U.recovered.union_subset_E
  have hsquare : (U.recovered.family.unionCells.card : ℝ)^2 ≤ (E.card : ℝ)^2 :=
    pow_le_pow_left₀ (Nat.cast_nonneg _) hcard 2
  have hcap : capCoefficient (k:=k+1) (width:=width) d Cball =
      geometricFactor k width baseRadius d*L := cap_factorization k width baseRadius d L
  rw [hcap] at henergy
  refine ⟨rho,hrho,hlower,?_⟩
  calc
    _ = c₀*kap^5*(geometricFactor k width baseRadius d*L)⁻¹*
          rho^r*δ^(d-d'+1+eps)*(outputSupport U.selection.retained).card := by
      dsimp only [c,L]
      simp only [div_eq_mul_inv,mul_inv_rev]
      ring
    _ ≤ (U.recovered.family.unionCells.card : ℝ)^2 := henergy
    _ ≤ (E.card : ℝ)^2 := hsquare


variable {k M : ℕ} {F : TubeFamily (k+2) M} {E : Finset (Cell (k+2))}
    {marks : Fin M → Finset (Cell (k+2))}
    {K δ A lam xi B theta width baseRadius m d p eps alpha kap : ℝ}
    (U : Package F E marks K δ A lam xi B theta width baseRadius m d p eps alpha kap)

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
closing input is supplied by `energy` on this same package. -/
theorem fourth_power {d' q cBase cClose rho : ℝ}
    (hK : 0 < K) (hBase : 0 < cBase) (hClose : 0 < cClose)
    (hA : 0 < A) (hlam : 0 < lam) (hxi : 0 < xi) (hxi1 : xi ≤ 1) (hM : 0 < M)
    (hp : 1 ≤ p) (hq : 2 ≤ q) (heps : 0 ≤ eps) (heps1 : eps ≤ 1)
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
end KakeyaFormal.AdmissiblePivotClosing
