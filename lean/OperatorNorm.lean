import OperatorStrongEstimate

/-! Literal Mathlib Lp-norm assertions for the actual Kakeya operator. The
input may be any a.e.-measurable real function, and all constants precede the
scale and input. No interpolation theorem remains as an assumed premise. -/
namespace KakeyaFormal.OperatorNorm
open MeasureTheory KakeyaOperator OperatorScaleAlgebra OperatorNormConversion
open scoped ENNReal
noncomputable section
set_option maxHeartbeats 1000000

def NonnegativeEstimate (n : ℕ) (a : ℝ) : Prop :=
  ∀ eps : ℝ, 0 < eps → ∃ C : ℝ, 0 < C ∧ ∀ {δ : ℝ}, 0 < δ → δ ≤ 1 →
    ∀ f : Space n → ℝ≥0∞, Measurable f →
      eLpNorm (maximal δ f) (ENNReal.ofReal a) (sphereMeasure n) ≤
        ENNReal.ofReal (C*δ^(1-(n:ℝ)/a-eps))*eLpNorm f (ENNReal.ofReal a) volume

/-- The actual strong norm estimate (9.8), using absolute tube averages,
the actual sphere measure, and Mathlib eLpNorm on input and output. -/
def Estimate (n : ℕ) (a : ℝ) : Prop :=
  ∀ eps : ℝ, 0 < eps → ∃ C : ℝ, 0 < C ∧ ∀ {δ : ℝ}, 0 < δ → δ ≤ 1 →
    ∀ f : Space n → ℝ, AEMeasurable f volume →
      eLpNorm (normMaximal δ f) (ENNReal.ofReal a) (sphereMeasure n) ≤
        ENNReal.ofReal (C*δ^(1-(n:ℝ)/a-eps))*eLpNorm f (ENNReal.ofReal a) volume

theorem from_restricted_weak {k : ℕ} {a : ℝ}
    (hestimate : OperatorRestrictedWeak.Estimate (k+1) a) (ha : 1 < a) :
    NonnegativeEstimate (k+1) a := by
  intro eps heps
  have hchoice := choices_positive ha heps
  obtain ⟨K,hK,hbound⟩ := OperatorStrongEstimate.interpolated_moment
    hestimate ha hchoice.1 hchoice.2
  have ha0 : 0 < a := by linarith
  refine ⟨K^(1/a),Real.rpow_pos_of_pos hK _,?_⟩
  intro δ hδ hδ1 f hf
  have hh := scaled_moment_to_norm volume (sphereMeasure (k+1)) f (maximal δ f)
    ha0 hK hδ (hbound hδ hδ1 f hf)
  have hs := chosen_scale_le ((k+1:ℕ):ℝ) ha heps hδ hδ1
  have heq : -((((k+1:ℕ):ℝ)-a)/a)-eps = 1-((k+1:ℕ):ℝ)/a-eps := by
    field_simp
    ring
  rw [heq] at hs
  exact hh.trans (mul_le_mul'
    (ENNReal.ofReal_le_ofReal (mul_le_mul_of_nonneg_left hs (Real.rpow_nonneg hK.le _))) le_rfl)

/-- Null-set changes affect no actual tube average. A measurable
representative therefore extends the norm bound to a.e.-measurable real inputs. -/
theorem nonnegative_to_real {k : ℕ} {a : ℝ}
    (h : NonnegativeEstimate (k+1) a) : Estimate (k+1) a := by
  intro eps heps
  obtain ⟨C,hC,hbound⟩ := h eps heps
  refine ⟨C,hC,?_⟩
  intro δ hδ hδ1 f hf
  let g : Space (k+1) → ℝ≥0∞ := fun x => ENNReal.ofReal |f x|
  have hg : AEMeasurable g volume := hf.abs.ennreal_ofReal
  have heq : normMaximal δ f = maximal δ (hg.mk g) :=
    funext (fun v => KakeyaOperatorLaws.maximal_ae_congr δ hg.ae_eq_mk v)
  rw [heq]
  have hh := hbound hδ hδ1 (hg.mk g) hg.measurable_mk
  rw [← eLpNorm_congr_ae hg.ae_eq_mk] at hh
  simpa only [g,norm_ofReal_abs] using hh

/-- The literal measurable-shading assertion supplies the actual operator
norm theorem through entirely proved geometry and both interpolation stages. -/
theorem from_shading {k : ℕ} {a : ℝ}
    (h : MaximalShading.Estimate (k+1) a) (ha : 1 < a) : Estimate (k+1) a :=
  nonnegative_to_real (from_restricted_weak (OperatorRestrictedWeak.from_shading (by omega) h) ha)

end
end KakeyaFormal.OperatorNorm
