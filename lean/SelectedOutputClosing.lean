import SelectedOutputWitness
import SelectedOutputDensity

/-! Closing the actual retained selected-output energy in the original scale.
The normalized meshes in the geometric witnesses are converted by a fixed
factor before the original output-population and cutoff substitutions. -/
namespace KakeyaFormal.SelectedOutputClosing
open Finset ActualLabelSelection AngleFiberSelection LegalAngleSamples
open SelectedOutputPairs SelectedOutputSlabs SelectedLiftWitness SlabNormalization
open ActualGroupedIncidence ClosingEnergyAlgebra
open scoped BigOperators
noncomputable section
open Classical

/-- Both the original and normalized scales are explicit. The exponent may
have either sign; the positive homothety factor is kept in the constant. -/
theorem normalization_identity {δ R kappa c A rho r t Q : ℝ}
    (hδ : 0 < δ) (hR : 0 < R) :
    (c/R^((5:ℝ)+t))*kappa^5*A⁻¹*rho^r*δ^t*Q =
      c*(kappa/R)^5*A⁻¹*rho^r*(δ/R)^t*Q := by
  rw [Real.rpow_add hR,Real.rpow_ofNat,div_pow,Real.div_rpow hδ.le hR.le]
  field_simp

def originalCoefficient (k : ℕ) (width c J r t : ℝ) : ℝ :=
  closingCoefficient c (pivotCoefficient (k+1) (errorConstant (k+1) (2*width)))
    (liftCoefficient (k+1) (errorConstant (k+1) (2*width))) J r /
      (1+2*width)^((5:ℝ)+t)

theorem originalCoefficient_pos (k : ℕ) {width c J r t : ℝ}
    (hw : 0 ≤ width) (hc : 0 < c) (hJ : 0 < J) :
    0 < originalCoefficient k width c J r t := by
  have hC : 0 < errorConstant (k+1) (2*width) := by dsimp [errorConstant]; positivity
  have hh := closingCoefficient_pos (r:=r) hc
    (pivotCoefficient_pos (k+1) hC.le) (liftCoefficient_pos (k+1) hC) hJ
  dsimp [originalCoefficient]
  positivity

variable {k M : ℕ} {F : TubeFamily (k+1) M} {H : Finset (Cell (k+1))}
    {δ lam kappa width : ℝ} {S : SampleSystem F H δ lam kappa width}
    {hkappa : 0 < kappa} {hwidth : 0 ≤ width} {hadm : F.Admissible width δ}
    (P : Selection S hkappa hwidth hadm)
    (D : ∀ q : Index P, LineData P q)
    {C : Type*} (color : Index P → C) (shading : Index P → Finset (Cell (k+2)))

/-- Actual selected-output witnesses close the same retained incidence set
returned by grouped pruning. The conclusion already uses original delta and
kappa, with the exact homothety cost inside a fixed positive coefficient. -/
theorem retained_closing {c J A d d' eps r : ℝ}
    (hδ : 0 < δ) (hδ1 : δ ≤ 1) (hkappa1 : kappa ≤ 1)
    (hc : 0 < c) (hJ : 0 < J) (hA : 0 < A)
    (hsub : ∀ q, shading q ⊆ (D q).cells.image (shiftCell (δ/(1+2*width)) (D q).slab))
    (hmass : ∀ q, (commonK P:ℝ)/3 ≤ ((shading q).card:ℝ))
    (hscale : 2*errorConstant (k+1) (2*width)*(δ/(1+2*width)) ≤
      (kappa/(1+2*width))^5/4)
    (T : Finset (GroupedCumulative.Record (k:=k+2) (population (fun q => (D q).base P) color)))
    (hT : T ⊆ incidences (fun q => (D q).base P) color shading)
    (hretain : ((incidences (fun q => (D q).base P) color shading).card:ℝ)/2 ≤ (T.card:ℝ))
    (hupper : (∑ p ∈ T.image (position (fun q => (D q).base P) color),
      (GroupedIncidence.degree T (position (fun q => (D q).base P) color) p:ℝ)^2) ≤
      ((2:ℝ)^(r+1)*J*(1/(δ/(1+2*width)))/
        ((c*A⁻¹*(δ/(1+2*width))^(d-d'+eps))*(SelectedOutputDensity.rho P D color shading)^(r-1)))*
      (T.card:ℝ)) :
    originalCoefficient k width c J r (d-d'+1+eps)*kappa^5*A⁻¹*
      (SelectedOutputDensity.rho P D color shading)^r*δ^(d-d'+1+eps)*
      (outputSupport P.retained).card ≤ (F.unionCells.card:ℝ)^2 := by
  have hR : 0 < 1+2*width := by linarith
  have hQ := SelectedOutputDensity.output_card_pos P
  have hrho := SelectedOutputDensity.rho_pos P D color shading hδ hmass
  have hC : 0 < errorConstant (k+1) (2*width) := by dsimp [errorConstant]; positivity
  have hmass' : SelectedOutputDensity.rho P D color shading*(1/(δ/(1+2*width)))*
      (outputSupport P.retained).card/2 ≤ (T.card:ℝ) := by
    have hid : SelectedOutputDensity.rho P D color shading*(1/(δ/(1+2*width)))*
        (outputSupport P.retained).card/2 =
        ((incidences (fun q => (D q).base P) color shading).card:ℝ)/2 := by
      dsimp [SelectedOutputDensity.rho]
      field_simp
    rwa [hid]
  have hh := closing_energy hrho hQ (div_pos hδ hR) (div_pos hkappa hR) hc
    (pivotCoefficient_pos (k+1) hC.le) (liftCoefficient_pos (k+1) hC) hJ hA hmass' hupper
    (SelectedOutputWitness.retained_energy P D color shading hsub hδ hδ1 hkappa1 hscale T hT)
  rw [← normalization_identity hδ hR] at hh
  exact hh

end
end KakeyaFormal.SelectedOutputClosing
