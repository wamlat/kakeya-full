import GaussianRealization
import GaussianCollisionSelection
import GaussianSelectionAlgebra

/-! A single actual Gaussian projection and an actual separated subfamily.
Probability, collision count and graph hypotheses are discharged internally. -/
namespace KakeyaFormal.GaussianProjectedSelection
open GaussianMatrix GaussianLinearOperator GaussianConditioning GaussianCollisionExpectation
open GaussianCollisionSelection GaussianSelectionAlgebra
noncomputable section

def retainedConstant : ℝ := populationConstant (expectationCoefficient 20)

theorem retainedConstant_pos : 0 < retainedConstant :=
  populationConstant_pos (expectationCoefficient_pos 20)

/-- The original cap-four and separation inputs construct one bounded map
and an actual original-index subset of size at least c M/(A log(2/delta)).
Every retained image is nonzero and the projected directions are separated.
All constants precede the family, scale and cap coefficient. -/
theorem exists_projection {M : ℕ} (F : TubeFamily 7 M) {δ A : ℝ}
    (hδ : 0 < δ) (hδ1 : δ ≤ 1) (hA : 1 ≤ A)
    (hsep : F.Separated δ) (hcap : F.CapBound δ 4 A) :
    ∃ ω : Sample 5 7, ∃ S : Finset (Fin M),
      ‖operator ω‖ ≤ 20 ∧
      (∀ i∈S, (1/4:ℝ) ≤ ‖operator ω (F.tube i).direction‖) ∧
      (∀ i∈S, ∀ j∈S, i≠j → δ <
        ProjectiveAngleComparison.angle (unitDirection (operator ω (F.tube i).direction))
          (unitDirection (operator ω (F.tube j).direction))) ∧
      (∀ i∈S, ∀ j∈S, i≠j → (2/Real.pi)*δ ≤
        projectiveDistance (unitDirection (operator ω (F.tube i).direction))
          (unitDirection (operator ω (F.tube j).direction))) ∧
      retainedConstant*(M:ℝ)/(A*Real.log (2/δ)) ≤ (S.card:ℝ) := by
  obtain ⟨ω,hK,hV,hgood,hE⟩ := GaussianRealization.exists_matrix F hδ hδ1 hA hsep hcap
  obtain ⟨S,hsub,hangle,hchord,hsize⟩ := select F δ ω hK
  have hVhi : (good F ω).card ≤ M := by
    simpa only [Fintype.card_fin] using Finset.card_le_univ (good F ω)
  have hcount : ((orderedCollisions F 20 δ ω).card:ℝ) ≤
      4*expectationCoefficient 20*A*(M:ℝ)*Real.log (2/δ) := by
    simpa only [GaussianRealization.budget,mul_assoc] using hE
  have hlog : Real.log 2 ≤ Real.log (2/δ) :=
    Real.log_le_log (by norm_num) ((le_div_iff₀ hδ).mpr (by linarith))
  have hp := cardinality_lower hV hVhi hcount (expectationCoefficient_pos 20) hA hlog
  exact ⟨ω,S,hK,fun i hi => hgood i (hsub hi),hangle,hchord,hp.trans hsize⟩

end
end KakeyaFormal.GaussianProjectedSelection
