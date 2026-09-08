import MarkedSubsetSamples
import PivotOutputLowerBound

/-! Original sparse marks, full-shading two ends, actual legal samples and
geometric collisions produce the same selected output family and its lower
bound. No angle-population, sample-system or collision premise remains. -/
namespace KakeyaFormal.MarkedPivotSelection
open Finset TransverseAngles LegalAngleSamples ActualLabelSelection AngleFiberSelection
open MarkedSubsetSamples PivotOutputLowerBound PivotSelectionBudgets
open scoped BigOperators
noncomputable section

/-- The actual input-facing selection bound, with marked incidence I and
occupied-cell comparison E. The exact selected samples remain attached to the
returned full-family legal-sample system and output selection. -/
theorem construct {k M : ℕ} (F : TubeFamily (k+2) M)
    (marks : Fin M → Finset (Cell (k+2))) (H : Finset (Cell (k+2)))
    {δ lam width B alpha theta I E : ℝ}
    (hδ : 0 < δ) (hlam : 0 < lam) (hw : (1:ℝ)/12 ≤ width)
    (hB : 1 ≤ B) (ha : 0 < alpha) (htheta : 0 < theta) (htheta1 : theta ≤ 1)
    (hI : 0 < I) (hE : 0 < E)
    (hadm : F.Admissible width δ) (hcomp : F.Comparable δ lam) (hsep : F.Separated δ)
    (hsub : ∀ i, marks i ⊆ F.shade i)
    (hmass : I ≤ ∑ z ∈ H, ((incident (markedFamily F marks) z).card:ℝ))
    (hH : (H.card:ℝ) ≤ E)
    (hbroad : ∀ z ∈ H, ∀ v : Space (k+2), ‖v‖=1 →
      (((incident (markedFamily F marks) z).filter (fun i =>
        projectiveDistance (F.tube i).direction v < theta)).card:ℝ) ≤
          ((incident (markedFamily F marks) z).card:ℝ)/2)
    (hends : ∀ i, ∀ x : Space (k+2), ∀ r : ℝ, δ ≤ r → r ≤ 1 →
      (((F.shade i).filter (fun z => dist (cellCenter δ z) x ≤ r)).card:ℝ) ≤
        B*r^alpha*((F.shade i).card:ℝ))
    (hsmall : (6*width/(PivotKappa.choice width B theta⁻¹ alpha 1))*δ ≤ 1/2) :
    let kappa := PivotKappa.choice width B theta⁻¹ alpha 1
    let hk := (fixed_radius_choice (by linarith : 0 ≤ width) hB ha htheta htheta1).1
    ∃ S : SampleSystem F H δ lam kappa width,
    ∃ P : Selection S hk (by linarith : 0 ≤ width) hadm,
      let σ := ((2^P.level:ℕ):ℝ)*δ
      lam^2/(512*LegalSampleOutputs.outputConstant (k+2) width) < σ ∧
      σ ≤ fiberCoefficient (k+2) width/kappa ∧
      (outputCoefficient k width/16)*kappa^(5*(k+1))*lam^6*I^2/
        (σ^2*δ^2*(pivotLog δ)^3*E) ≤ ((outputSupport P.retained).card:ℝ) := by
  intro kappa hk
  have hw0 : 0 ≤ width := by linarith
  obtain ⟨_,hk100,_,_,_⟩ := fixed_radius_choice hw0 hB ha htheta htheta1
  have hk1 : kappa ≤ 1 := by dsimp [kappa]; linarith
  have hscale := scale_le_kappa hk hδ hw hsmall
  have hδ1 : δ ≤ 1 := hscale.trans hk1
  obtain ⟨⟨S⟩,hcount,hA⟩ := construct_fixed_radius F marks H hδ hlam hw0 hB ha htheta htheta1
    hI hE hadm hcomp hsub hmass hH hbroad hends hscale
  obtain ⟨P,hlo,hhi,hQ⟩ := construct_sigma S hA hδ hδ1 hlam hk hk1 hw hadm hcomp hsep hsmall
  refine ⟨S,P,hlo,hhi,?_⟩
  let σ := ((2^P.level:ℕ):ℝ)*δ
  have hC := outputCoefficient_pos k hw0
  have hL := zero_lt_one.trans_le (pivotLog_ge_one hδ hδ1)
  have hσ : 0 < σ := by
    have hh : (0:ℝ) < (2^P.level:ℕ) := by exact_mod_cast zero_lt_one.trans_le P.dyadic_pos
    dsimp [σ]
    positivity
  calc
    _ = ((outputCoefficient k width/8)*kappa^(5*(k+1))*lam^6/
        (σ^2*δ^2*(pivotLog δ)^3))*(I^2/(2*E)) := by dsimp [σ]; ring
    _ ≤ ((outputCoefficient k width/8)*kappa^(5*(k+1))*lam^6/
        (σ^2*δ^2*(pivotLog δ)^3))*((angles F H kappa).card:ℝ) :=
      mul_le_mul_of_nonneg_left hcount (by positivity)
    _ = (outputCoefficient k width/8)*kappa^(5*(k+1))*lam^6*((angles F H kappa).card:ℝ)/
        (σ^2*δ^2*(pivotLog δ)^3) := by ring
    _ ≤ _ := hQ

end
end KakeyaFormal.MarkedPivotSelection
