import TubeOpenCarrier

/-! Lower semicontinuity of actual nonnegative parameter integrals, proved
by Fatou's lemma. In particular, open tube integrals are jointly lower
semicontinuous in the original base and direction. -/
namespace KakeyaFormal.ParameterLIntegral
open MeasureTheory Set Filter
open scoped ENNReal Topology
noncomputable section
set_option maxHeartbeats 800000

theorem lowerSemicontinuous_lintegral
    {P X : Type*} [TopologicalSpace P] [FirstCountableTopology P]
    [MeasurableSpace X] (μ : Measure X) (K : P → X → ℝ≥0∞)
    (hK : ∀ p, Measurable (K p))
    (hlsc : ∀ x, LowerSemicontinuous (fun p => K p x)) :
    LowerSemicontinuous (fun p => ∫⁻ x, K p x ∂μ) := by
  apply lowerSemicontinuous_iff_le_liminf.mpr
  intro p
  exact (lintegral_mono (fun x => (hlsc x).le_liminf p)).trans
    (lintegral_liminf_le hK)

/-- Open parameter membership and measurable spatial sections suffice;
neither boundedness nor integrability of the nonnegative function is needed. -/
theorem lowerSemicontinuous_setLIntegral
    {P X : Type*} [TopologicalSpace P] [FirstCountableTopology P]
    [MeasurableSpace X] (μ : Measure X) (S : P → Set X)
    (hS : ∀ p, MeasurableSet (S p))
    (hopen : ∀ x, IsOpen {p | x ∈ S p})
    (f : X → ℝ≥0∞) (hf : Measurable f) :
    LowerSemicontinuous (fun p => ∫⁻ x in S p, f x ∂μ) := by
  have hi : LowerSemicontinuous (fun p => ∫⁻ x, (S p).indicator f x ∂μ) := by
    apply lowerSemicontinuous_lintegral μ
    · exact fun p => hf.indicator (hS p)
    · intro x
      have heq : (fun p => (S p).indicator f x) =
          ({p | x ∈ S p}).indicator (fun _ => f x) := by
        funext p
        rfl
      rw [heq]
      exact (hopen x).lowerSemicontinuous_indicator bot_le
  simpa only [lintegral_indicator (hS _) f] using hi

theorem open_tube_lintegral {n : ℕ} (δ : ℝ)
    (f : Space n → ℝ≥0∞) (hf : Measurable f) :
    LowerSemicontinuous (fun p : Space n × Space n =>
      ∫⁻ x in TubeOpenCarrier.openCarrier p.1 p.2 δ, f x ∂volume) :=
  lowerSemicontinuous_setLIntegral (P:=Space n × Space n) (X:=Space n)
    (volume : Measure (Space n))
    (fun p : Space n × Space n => TubeOpenCarrier.openCarrier p.1 p.2 δ)
    (fun p => (TubeOpenCarrier.openCarrier_isOpen p.1 p.2 δ).measurableSet)
    (fun x => TubeOpenCarrier.parameter_membership_isOpen x δ) f hf

end
end KakeyaFormal.ParameterLIntegral
