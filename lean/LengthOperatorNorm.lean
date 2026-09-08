import LengthOperatorBound

/-! Actual strong maximal-operator bounds for the supremum over every position
and every axis length in one fixed positive interval, with the actual carrier
volume in every denominator. Input values may be real, complex or normed. -/
namespace KakeyaFormal.LengthOperatorNorm
open MeasureTheory KakeyaOperator MaximalLengths
open scoped ENNReal
noncomputable section

def normMaximal {n : ℕ} {X : Type*} [Norm X]
    (lower upper width δ : ℝ) (f : Space n → X) : Direction n → ℝ≥0∞ :=
  LengthOperatorGeometry.maximal lower upper width δ (fun x => ENNReal.ofReal ‖f x‖)

theorem normMaximal_measurable {k : ℕ} {X : Type*} [NormedAddCommGroup X]
    [MeasurableSpace X] [BorelSpace X] {l u width δ : ℝ}
    (hl : 0 < l) (hw : 0 < width) (hδ : 0 < δ)
    (f : Space (k+1) → X) (hf : AEMeasurable f volume) :
    Measurable (normMaximal l u width δ f) :=
  LengthOperatorGeometry.maximal_measurable hl hw hδ _ hf.norm.ennreal_ofReal

def factor (n : ℕ) (a lower upper width : ℝ) : ℝ :=
  (upperScale upper width)^n/(lowerScale lower width)^n *
    (upperScale upper width)^(-(n:ℝ)/a)

theorem factor_pos (n : ℕ) (a : ℝ) {l u width : ℝ} (hl : 0 < l) (hw : 0 < width) :
    0 < factor n a l u width := by
  obtain ⟨hs,_,_,_,hW,_,_⟩ := scale_bounds (lengthUpper:=u) hl hw
  have hWp : 0 < upperScale u width := zero_lt_one.trans_le hW
  unfold factor
  positivity

/-- A genuine norm theorem with all geometric constants fixed before delta
and the input; it includes real and complex a.e.-measurable inputs. -/
def Estimate (n : ℕ) (a : ℝ) : Prop :=
  ∀ lower upper width : ℝ, 0 < lower → 0 < width →
    ∀ eps : ℝ, 0 < eps → ∃ C : ℝ, 0 < C ∧ ∀ {δ : ℝ}, 0 < δ → δ ≤ 1 →
    ∀ {X : Type} [NormedAddCommGroup X] [MeasurableSpace X] [BorelSpace X]
      (f : Space n → X), AEMeasurable f volume →
      eLpNorm (normMaximal lower upper width δ f) (ENNReal.ofReal a) (sphereMeasure n) ≤
        ENNReal.ofReal (C*δ^(1-(n:ℝ)/a-eps))*eLpNorm f (ENNReal.ofReal a) volume

theorem from_unit {k : ℕ} {a : ℝ} (ha : 0 < a)
    (h : OperatorNorm.Estimate (k+1) a) : Estimate (k+1) a := by
  intro l u width hl hw eps heps
  obtain ⟨c,hc,hbound⟩ := h eps heps
  obtain ⟨hs,_,_,_,hW,_,_⟩ := scale_bounds (lengthUpper:=u) hl hw
  have hWp : 0 < upperScale u width := zero_lt_one.trans_le hW
  let W := upperScale u width
  let D := W^(k+1)/(lowerScale l width)^(k+1)
  have hD : 0 < D := div_pos (pow_pos hWp _) (pow_pos hs _)
  refine ⟨c*factor (k+1) a l u width,mul_pos hc (factor_pos _ _ hl hw),?_⟩
  intro δ hδ hδ1 X _ _ _ f hf
  let g : Space (k+1) → ℝ := fun x => ‖f (W • x)‖
  have hg : AEMeasurable g volume := (DilationIntegral.aemeasurable_comp hWp hf).norm
  have hpoint (v : Direction (k+1)) :
      normMaximal l u width δ f v ≤ ENNReal.ofReal D*KakeyaOperator.normMaximal δ g v := by
    simpa only [normMaximal,KakeyaOperator.normMaximal,g,abs_norm,W,D] using
      LengthOperatorBound.maximal_le_unit hl hw hδ.le (fun x => ENNReal.ofReal ‖f x‖) v
  have hnorm : eLpNorm (normMaximal l u width δ f) (ENNReal.ofReal a) (sphereMeasure (k+1)) ≤
      ENNReal.ofReal D*eLpNorm (KakeyaOperator.normMaximal δ g) (ENNReal.ofReal a)
        (sphereMeasure (k+1)) := by
    have hh := eLpNorm_le_mul_eLpNorm_of_ae_le_mul'
      (f:=normMaximal l u width δ f) (g:=KakeyaOperator.normMaximal δ g)
      (μ:=sphereMeasure (k+1)) (c:=NNReal.mk D hD.le)
      (Filter.Eventually.of_forall (fun v => by
        simpa only [enorm_eq_self,← ENNReal.ofReal_eq_coe_nnreal hD.le] using hpoint v))
      (ENNReal.ofReal a)
    simpa only [← ENNReal.ofReal_eq_coe_nnreal hD.le] using hh
  have hh := hnorm.trans (mul_le_mul' le_rfl (hbound hδ hδ1 g hg))
  have hn : eLpNorm g (ENNReal.ofReal a) volume =
      ENNReal.ofReal (W^(-((k+1:ℕ):ℝ)/a))*eLpNorm f (ENNReal.ofReal a) volume := by
    dsimp [g]
    rw [eLpNorm_norm]
    exact DilationIntegral.norm_comp hWp ha f
  rw [hn] at hh
  have hp : 0 < δ^(1-((k+1:ℕ):ℝ)/a-eps) := Real.rpow_pos_of_pos hδ _
  have hfac : c*factor (k+1) a l u width*δ^(1-((k+1:ℕ):ℝ)/a-eps) =
      D*(c*δ^(1-((k+1:ℕ):ℝ)/a-eps))*W^(-((k+1:ℕ):ℝ)/a) := by
    dsimp [factor,D,W]
    ring
  rw [hfac,ENNReal.ofReal_mul (mul_nonneg hD.le (mul_nonneg hc.le hp.le)),
    ENNReal.ofReal_mul hD.le]
  simpa only [mul_assoc] using hh

/-- The main endpoint for arbitrary fixed length/width conventions and
arbitrary positions, as an actual length-and-position operator supremum. -/
theorem endpoint_formula {n : ℕ} (hn : 6 ≤ n) :
    Estimate n (3+(2-Real.sqrt 2)*((n:ℝ)-4)) := by
  have hroot : 0 < 2-Real.sqrt 2 := by
    have hs := Real.sq_sqrt (show (0:ℝ) ≤ 2 by norm_num)
    have hh := Real.sqrt_nonneg (2:ℝ)
    nlinarith
  have hdim : 0 ≤ (n:ℝ)-4 := by
    have hh : (6:ℝ) ≤ n := by exact_mod_cast hn
    linarith
  have ha : 0 < 3+(2-Real.sqrt 2)*((n:ℝ)-4) := by
    nlinarith [mul_nonneg hroot.le hdim]
  cases n with
  | zero => omega
  | succ k => exact from_unit ha (MainOperator.endpoint_formula hn)

theorem endpoint {n : ℕ} (hn : 6 ≤ n) :
    Estimate n (KakeyaScalar.limitProfile ((n:ℝ)-1)) := by
  have heq : KakeyaScalar.limitProfile ((n:ℝ)-1) = 3+(2-Real.sqrt 2)*((n:ℝ)-4) := by
    dsimp [KakeyaScalar.limitProfile,KakeyaScalar.slopeLimit]
    ring
  rw [heq]
  exact endpoint_formula hn

theorem six_first : Estimate 6 (33/8) := from_unit (by norm_num) MainOperator.six_first

theorem six_endpoint : Estimate 6 (7-2*Real.sqrt 2) := by
  apply from_unit _ MainOperator.six_endpoint
  have hs := Real.sq_sqrt (show (0:ℝ) ≤ 2 by norm_num)
  have hh := Real.sqrt_nonneg (2:ℝ)
  nlinarith

theorem eight_endpoint : Estimate 8 (11-4*Real.sqrt 2) := by
  apply from_unit _ MainOperator.eight_endpoint
  have hs := Real.sq_sqrt (show (0:ℝ) ≤ 2 by norm_num)
  have hh := Real.sqrt_nonneg (2:ℝ)
  nlinarith

end
end KakeyaFormal.LengthOperatorNorm
