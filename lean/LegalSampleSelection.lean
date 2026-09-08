import LegalSampleOutputs

/-! Actual geometric sample and output budgets instantiate low-fiber deletion
and the global integer dyadic bin, without any assumed counting bound. -/
namespace KakeyaFormal.LegalSampleSelection
open Finset LegalAngleSamples LegalSampleOutputs TransverseAngles AngleFiberSelection PivotOutputCount
open scoped BigOperators
noncomputable section
open Classical

def sampleBudget (lam δ : ℝ) : ℝ := (lam/δ)^3/128
def outputBudget (k : ℕ) (width lam δ : ℝ) : ℝ := outputConstant k width*lam/δ^2
def cutoff (k : ℕ) (width lam δ : ℝ) : ℝ := lam^2/(256*outputConstant k width*δ)
def fiberBudget (k : ℕ) (width kappa δ : ℝ) : ℕ :=
  Nat.ceil ((fiberConstant k (2*width)*(1+2*width)^2)/(kappa*δ))

theorem cutoff_calibration {k : ℕ} {width lam δ : ℝ}
    (hwidth : 0 ≤ width) (hδ : 0 < δ) :
    cutoff k width lam δ*outputBudget k width lam δ = sampleBudget lam δ/2 := by
  have hD := (outputConstant_pos k hwidth).ne'
  dsimp [cutoff,outputBudget,sampleBudget]
  field_simp
  ring

/-- One actual global bin of whole angle-output edges is constructed from the
original tube geometry. It has the precise threshold, integer budget, retained
sample mass and edge count required by (5.14). -/
theorem dyadic_selection {k M : ℕ} {F : TubeFamily k M} {H : Finset (Cell k)}
    {δ lam kappa width : ℝ} (S : SampleSystem F H δ lam kappa width)
    (hA : (angles F H kappa).Nonempty)
    (hδ : 0 < δ) (hδ1 : δ ≤ 1) (hlam : 0 < lam)
    (hkappa : 0 < kappa) (hkappa1 : kappa ≤ 1) (hwidth : 0 ≤ width)
    (hadm : F.Admissible width δ) (hcomp : F.Comparable δ lam) :
    let A : Finset ↥(angles F H kappa) := univ
    let out := fun a => output S a hkappa hwidth hadm
    let B := fiberBudget k width kappa δ
    let t := cutoff k width lam δ
    let mu := sampleBudget lam δ
    ∃ j ≤ Nat.log 2 B, ∃ Ω : Finset (↥(angles F H kappa) × (Cell k × Cell k)),
      Ω = (goodEdges A S.samples out t).filter (fun e => 2^j ≤ size S.samples out e ∧ size S.samples out e < 2*(2^j)) ∧
      Ω.Nonempty ∧ t/2 < (2^j : ℕ) ∧ (2^j : ℕ) ≤ B ∧
      mu*(A.card:ℝ)/(2*(Nat.log 2 B+1:ℕ)) ≤ ∑ e ∈ Ω, (size S.samples out e:ℝ) ∧
      mu*(A.card:ℝ)/(4*(2^j:ℕ)*(Nat.log 2 B+1:ℕ)) ≤ (Ω.card:ℝ) := by
  dsimp only
  have hA' : (univ : Finset ↥(angles F H kappa)).Nonempty := by
    obtain ⟨a,ha⟩ := hA
    exact ⟨⟨a,ha⟩,mem_univ _⟩
  have hmu : 0 < sampleBudget lam δ := by dsimp [sampleBudget]; positivity
  have ht : 0 ≤ cutoff k width lam δ := by
    have := outputConstant_pos k hwidth
    dsimp [cutoff]
    positivity
  apply dyadic_edge_selection univ S.samples (fun a => output S a hkappa hwidth hadm)
    hA' (U := outputBudget k width lam δ) hmu ht
  · intro a _
    exact S.card_lower a
  · intro a _
    have hh := density_output_count S a hδ hδ1 hkappa hwidth hadm hcomp
    unfold AngleFiberSelection.outputs outputBudget
    convert hh using 1
    congr 3
    exact Subsingleton.elim _ _
  · exact (cutoff_calibration hwidth hδ).le
  · intro e _
    simpa only [size,fiber,fiberBudget] using
      integer_fiber_count S e.1 e.2 hδ hδ1 hkappa hkappa1 hwidth hadm

end
end KakeyaFormal.LegalSampleSelection
