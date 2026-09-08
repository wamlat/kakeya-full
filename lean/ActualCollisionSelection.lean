import ActualLabelSelection
import CollisionEnergy

/-! Actual sample selection and geometric collisions supply the distinct-output
population together, without a supplied energy or output-population premise. -/
namespace KakeyaFormal.ActualCollisionSelection
open Finset TransverseAngles LegalAngleSamples LegalSampleSelection
open AngleFiberSelection ActualLabelSelection
noncomputable section

/-- All legal-sample, frequency-selection and collision bounds are applied to
the same constructed selection. Its exact single-angle fiber representatives
are the fields of the returned record, ready for the selected-lift construction. -/
theorem construct {k M : ℕ} {F : TubeFamily (k+2) M} {H : Finset (Cell (k+2))}
    {δ lam kappa width : ℝ} (S : SampleSystem F H δ lam kappa width)
    (hA : (angles F H kappa).Nonempty)
    (hδ : 0 < δ) (hδ1 : δ ≤ 1) (hlam : 0 < lam)
    (hk : 0 < kappa) (hk1 : kappa ≤ 1) (hw : 0 ≤ width)
    (hadm : F.Admissible width δ) (hcomp : F.Comparable δ lam) (hsep : F.Separated δ)
    (hsmall : (6*width/kappa)*δ ≤ 1/2) :
    ∃ P : Selection S hk hw hadm,
      let E := CollisionEnergy.rowConstant k width*(Real.logb 2 (2/δ)+2)*
        ((angles F H kappa).card:ℝ)/(kappa^(k+1)*δ^2)
      collisionEnergy P.retained ≤ E ∧
      (sampleBudget lam δ*((angles F H kappa).card:ℝ)/
        (4*(2^P.level:ℕ)*(Nat.log 2 (fiberBudget (k+2) width kappa δ)+1:ℕ)*
          labelBudget (k+1) width kappa))^2/E ≤ ((outputSupport P.retained).card:ℝ) := by
  obtain ⟨P⟩ := ActualLabelSelection.construct S hA hδ hδ1 hlam hk hk1 hw hadm hcomp hsep
  refine ⟨P,?_⟩
  intro E
  have henergy := CollisionEnergy.collision_energy_bound S hδ hδ1 hk hk1 hw hadm hsep hsmall
    P.retained P.retained_subset_actual P.same_second
  have hE : 0 < E := by
    have hC := CollisionEnergy.rowConstant_pos k hw
    have hcard : (0:ℝ) < (angles F H kappa).card := by exact_mod_cast card_pos.mpr hA
    have hlog := Real.logb_nonneg (by norm_num : (1:ℝ) < 2)
      ((le_div_iff₀ hδ).mpr (by linarith) : (1:ℝ) ≤ 2/δ)
    dsimp [E]
    positivity
  exact ⟨henergy,P.support_of_energy E hE henergy⟩

end
end KakeyaFormal.ActualCollisionSelection
