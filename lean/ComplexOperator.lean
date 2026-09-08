import MainOperator

/-! The same actual absolute-average operator and norm conclusions for complex
inputs. Only the scalar norm of the input enters the tube integrals, so the
already proved real-input theorem applies without changing any constant,
original tube, direction measure, scale exponent or a.e. hypothesis. -/
namespace KakeyaFormal.ComplexOperator
open MeasureTheory KakeyaOperator
open scoped ENNReal
noncomputable section

def maximal {n : ℕ} (δ : ℝ) (f : Space n → ℂ) : Direction n → ℝ≥0∞ :=
  KakeyaOperator.maximal δ (fun x => ENNReal.ofReal ‖f x‖)

theorem maximal_eq_norm {n : ℕ} (δ : ℝ) (f : Space n → ℂ) :
    maximal δ f = normMaximal δ (fun x => ‖f x‖) := by
  funext v
  simp only [maximal,KakeyaOperator.normMaximal,abs_norm]

/-- Source (9.8) with complex a.e.-measurable inputs, actual complex input
eLpNorm and actual absolute tube averages. -/
def Estimate (n : ℕ) (a : ℝ) : Prop :=
  ∀ eps : ℝ, 0 < eps → ∃ C : ℝ, 0 < C ∧ ∀ {δ : ℝ}, 0 < δ → δ ≤ 1 →
    ∀ f : Space n → ℂ, AEMeasurable f volume →
      eLpNorm (maximal δ f) (ENNReal.ofReal a) (sphereMeasure n) ≤
        ENNReal.ofReal (C*δ^(1-(n:ℝ)/a-eps))*eLpNorm f (ENNReal.ofReal a) volume

theorem from_real {n : ℕ} {a : ℝ} (h : OperatorNorm.Estimate n a) : Estimate n a := by
  intro eps heps
  obtain ⟨C,hC,hbound⟩ := h eps heps
  refine ⟨C,hC,?_⟩
  intro δ hδ hδ1 f hf
  have hh := hbound hδ hδ1 (fun x => ‖f x‖) hf.norm
  simpa only [← maximal_eq_norm,eLpNorm_norm] using hh

theorem six_first : Estimate 6 (33/8) := from_real MainOperator.six_first

theorem endpoint_formula {n : ℕ} (hn : 6 ≤ n) :
    Estimate n (3+(2-Real.sqrt 2)*((n:ℝ)-4)) := from_real (MainOperator.endpoint_formula hn)

theorem endpoint {n : ℕ} (hn : 6 ≤ n) :
    Estimate n (KakeyaScalar.limitProfile ((n:ℝ)-1)) := from_real (MainOperator.endpoint hn)

theorem six_endpoint : Estimate 6 (7-2*Real.sqrt 2) := from_real MainOperator.six_endpoint

theorem eight_endpoint : Estimate 8 (11-4*Real.sqrt 2) := from_real MainOperator.eight_endpoint

theorem six_diagonal_limit : Estimate 6 (29/7) := from_real MainOperator.six_diagonal_limit

theorem eight_diagonal_limit : Estimate 8 (37/7) := from_real MainOperator.eight_diagonal_limit

end
end KakeyaFormal.ComplexOperator
