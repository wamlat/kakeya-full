import MinPivotKappa
import PivotOutputLowerBound

/-! Actual original marked incidences to selected output fibers for an arbitrary
legal pivot radius. Scalar radius tests are explicit. No angle population,
sample-system, output count or collision-energy premise is assumed. -/
namespace KakeyaFormal.GenericMarkedPivotSelection
open Finset TransverseAngles LegalAngleSamples ActualLabelSelection AngleFiberSelection
open MarkedSubsetSamples PivotOutputLowerBound PivotSelectionBudgets
open scoped BigOperators
noncomputable section

/-- The actual input-facing selection bound, with marked incidence I and
occupied-cell comparison E. The exact selected samples remain attached to the
returned full-family legal-sample system and output selection. -/
theorem construct {k M : ℕ} (F : TubeFamily (k+2) M)
    (marks : Fin M → Finset (Cell (k+2))) (H : Finset (Cell (k+2)))
    {δ lam width B alpha theta kappa I E : ℝ}
    (hδ : 0 < δ) (hlam : 0 < lam) (hw : (1:ℝ)/12 ≤ width)
    (hk : 0 < kappa) (hk1 : kappa ≤ 1) (hangle : 2*kappa ≤ theta)
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
    (hradius : (2*width+1)*kappa ≤ 1)
    (hlegal : B*((2*width+1)*kappa)^alpha ≤ 1/16)
    (hsmall : (6*width/kappa)*δ ≤ 1/2) :
    ∃ S : SampleSystem F H δ lam kappa width,
    ∃ P : Selection S hk (by linarith : 0 ≤ width) hadm,
      let σ := ((2^P.level:ℕ):ℝ)*δ
      lam^2/(512*LegalSampleOutputs.outputConstant (k+2) width) < σ ∧
      σ ≤ fiberCoefficient (k+2) width/kappa ∧
      (outputCoefficient k width/16)*kappa^(5*(k+1))*lam^6*I^2/
        (σ^2*δ^2*(pivotLog δ)^3*E) ≤ ((outputSupport P.retained).card:ℝ) := by
  have hw0 : 0 ≤ width := by linarith
  have hscale := scale_le_kappa hk hδ hw hsmall
  have hδ1 : δ ≤ 1 := hscale.trans hk1
  obtain ⟨⟨S⟩,hcount,hA⟩ := MarkedSubsetSamples.construct F marks H hδ hδ1 hlam hw0
    hI hE hscale hangle hadm hcomp hsub hmass hH hbroad hends hradius hlegal
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

/-- The literal manuscript-form minimum constructs actual original output
fibers. B is original, while the full family may already have coefficient 2B
after pruning. The collision cutoff is in this same minimum radius. -/
theorem construct_source {k M : ℕ} (F : TubeFamily (k+2) M)
    (marks : Fin M → Finset (Cell (k+2))) (H : Finset (Cell (k+2)))
    {δ lam width B alpha theta I E : ℝ}
    (hδ : 0 < δ) (hlam : 0 < lam) (hw : (1:ℝ)/12 ≤ width)
    (hB : 1 ≤ B) (ha : 0 < alpha) (htheta : 0 < theta)
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
        (2*B)*r^alpha*((F.shade i).card:ℝ))
    (hsmall : (6*width/MinPivotKappa.sourceChoice width B alpha theta)*δ ≤ 1/2) :
    let kappa := MinPivotKappa.sourceChoice width B alpha theta
    let hk := (MinPivotKappa.source_admissible (by linarith : 0 ≤ width) hB ha htheta).1
    ∃ S : SampleSystem F H δ lam kappa width,
    ∃ P : Selection S hk (by linarith : 0 ≤ width) hadm,
      let σ := ((2^P.level:ℕ):ℝ)*δ
      lam^2/(512*LegalSampleOutputs.outputConstant (k+2) width) < σ ∧
      σ ≤ fiberCoefficient (k+2) width/kappa ∧
      (outputCoefficient k width/16)*kappa^(5*(k+1))*lam^6*I^2/
        (σ^2*δ^2*(pivotLog δ)^3*E) ≤ ((outputSupport P.retained).card:ℝ) := by
  intro kappa hk
  have hw0 : 0 ≤ width := by linarith
  obtain ⟨_,hk100,hangle,hradius,hlegal⟩ := MinPivotKappa.source_admissible hw0 hB ha htheta
  have hk1 : kappa ≤ 1 := by dsimp [kappa]; linarith
  exact construct F marks H hδ hlam hw hk hk1 hangle hI hE hadm hcomp hsep hsub
    hmass hH hbroad hends hradius hlegal hsmall

end
end KakeyaFormal.GenericMarkedPivotSelection
