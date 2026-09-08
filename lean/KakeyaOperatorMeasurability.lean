import ParameterLIntegral
import TubeIsometryVolume
import KakeyaOperatorLaws

/-! Measurability of the actual uncountable tube supremum. Open and closed
capsules agree almost everywhere; their normalized nonnegative integrals are
jointly lower semicontinuous by Fatou, with a fixed geometric denominator. -/
namespace KakeyaFormal.KakeyaOperatorMeasurability
open MeasureTheory KakeyaOperator
open scoped ENNReal Topology
noncomputable section
set_option maxHeartbeats 800000

theorem average_eq_open_scaled {k : ℕ} {δ : ℝ} (hδ : 0 < δ)
    (f : Space (k+1) → ℝ≥0∞) (hf : Measurable f)
    (b : Space (k+1)) (v : Direction (k+1)) :
    average δ f b v = ∫⁻ x in TubeOpenCarrier.openCarrier b v.val δ,
      f x * (TubeIsometryVolume.referenceVolume k δ)⁻¹ ∂volume := by
  rw [TubeIsometryVolume.average_fixed_denominator,
    TubeOpenCarrier.carrier_lintegral_eq_open _ hδ,
    lintegral_mul_const _ hf,div_eq_mul_inv]
  rfl

theorem average_lowerSemicontinuous {k : ℕ} {δ : ℝ} (hδ : 0 < δ)
    (f : Space (k+1) → ℝ≥0∞) (hf : Measurable f) :
    LowerSemicontinuous (fun p : Space (k+1) × Direction (k+1) => average δ f p.1 p.2) := by
  have hg : Measurable (fun x => f x*(TubeIsometryVolume.referenceVolume k δ)⁻¹) :=
    hf.mul_const _
  have hl := ParameterLIntegral.open_tube_lintegral δ _ hg
  have hc : Continuous (fun p : Space (k+1) × Direction (k+1) => (p.1,p.2.val)) := by
    fun_prop
  have hh := hl.comp hc
  simpa only [Function.comp_def,← average_eq_open_scaled hδ f hf] using hh

theorem average_measurable {k : ℕ} {δ : ℝ} (hδ : 0 < δ)
    (f : Space (k+1) → ℝ≥0∞) (hf : Measurable f) :
    Measurable (fun p : Space (k+1) × Direction (k+1) => average δ f p.1 p.2) :=
  (average_lowerSemicontinuous hδ f hf).measurable

/-- The supremum is taken over all actual bases in Euclidean space. Its
lower semicontinuity follows from that of every fixed-base average. -/
theorem maximal_lowerSemicontinuous {k : ℕ} {δ : ℝ} (hδ : 0 < δ)
    (f : Space (k+1) → ℝ≥0∞) (hf : Measurable f) :
    LowerSemicontinuous (maximal δ f) := by
  change LowerSemicontinuous (fun v : Direction (k+1) =>
    ⨆ b : Space (k+1), average δ f b v)
  refine lowerSemicontinuous_iSup
    (f:=fun (b : Space (k+1)) (v : Direction (k+1)) => average δ f b v) (fun b => ?_)
  have hc : Continuous (fun v : Direction (k+1) => (b,v)) := by fun_prop
  have hl := (average_lowerSemicontinuous hδ f hf).comp hc
  exact hl

theorem maximal_measurable {k : ℕ} {δ : ℝ} (hδ : 0 < δ)
    (f : Space (k+1) → ℝ≥0∞) (hf : Measurable f) : Measurable (maximal δ f) :=
  (maximal_lowerSemicontinuous hδ f hf).measurable

theorem normMaximal_measurable {k : ℕ} {δ : ℝ} (hδ : 0 < δ)
    (f : Space (k+1) → ℝ) (hf : Measurable f) : Measurable (normMaximal δ f) :=
  maximal_measurable hδ _ hf.abs.ennreal_ofReal

/-- Global null-set changes leave every tube integral unchanged, so an
a.e.-measurable input still has a literally measurable, lower semicontinuous
output in every direction. -/
theorem maximal_lowerSemicontinuous_of_aemeasurable {k : ℕ} {δ : ℝ} (hδ : 0 < δ)
    (f : Space (k+1) → ℝ≥0∞) (hf : AEMeasurable f volume) :
    LowerSemicontinuous (maximal δ f) := by
  have heq : maximal δ f = maximal δ (hf.mk f) :=
    funext (fun v => KakeyaOperatorLaws.maximal_ae_congr δ hf.ae_eq_mk v)
  rw [heq]
  exact maximal_lowerSemicontinuous hδ _ hf.measurable_mk

theorem maximal_measurable_of_aemeasurable {k : ℕ} {δ : ℝ} (hδ : 0 < δ)
    (f : Space (k+1) → ℝ≥0∞) (hf : AEMeasurable f volume) : Measurable (maximal δ f) :=
  (maximal_lowerSemicontinuous_of_aemeasurable hδ f hf).measurable

theorem indicatorMaximal_measurable {k : ℕ} {δ : ℝ} (hδ : 0 < δ)
    (E : Set (Space (k+1))) (hE : MeasurableSet E) : Measurable (indicatorMaximal δ E) := by
  have heq : indicatorMaximal δ E =
      fun v => (maximal δ (E.indicator (fun _ => 1)) v).toReal := by
    funext v
    rw [KakeyaOperatorLaws.maximal_indicator hδ E hE,
      ENNReal.toReal_ofReal (indicatorMaximal_nonneg hδ E v)]
  rw [heq]
  exact (maximal_measurable hδ _ (measurable_const.indicator hE)).ennreal_toReal

theorem indicatorLevel_measurable {k : ℕ} {δ : ℝ} (hδ : 0 < δ)
    (E : Set (Space (k+1))) (hE : MeasurableSet E) (lam : ℝ) :
    MeasurableSet (indicatorLevel δ E lam) :=
  measurableSet_lt measurable_const (indicatorMaximal_measurable hδ E hE)

end
end KakeyaFormal.KakeyaOperatorMeasurability
