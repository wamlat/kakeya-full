import SamplingMeasurablePivot
import LowCellAbsorption

/-! The two sampling alternatives now give one actual measurable-input bound
at sufficiently small scales. The low-cell logarithms are absorbed using the
strict scale margin; the high-cell outcome is constructed and passed directly
to the marked pivot. No sampling result or desired population bound is an input. -/
namespace KakeyaFormal.SamplingHighDensity
open Finset SamplingNormalizedMeans SamplingSupport MeasureTheory
noncomputable section

/-- Weakening the physical two-ends exponent changes no full or marked set. -/
theorem input_weaken_alpha {n M : ℕ} {F : TubeFamily (n+1) M}
    {Full G : Fin M → Set (Space (n+1))} {δ width R lam c₀ C₀ xi B alpha alpha' K beta : ℝ}
    (h : Input F Full G δ width R lam c₀ C₀ xi B alpha K beta)
    (ha' : 0 ≤ alpha') (horder : alpha' ≤ alpha) :
    Input F Full G δ width R lam c₀ C₀ xi B alpha' K beta := by
  refine { h with two_ends_exponent := ha', two_ends := ?_ }
  intro i x r hr hr1
  have hpower := Real.rpow_le_rpow_of_exponent_ge (h.scale_pos.trans_le hr) hr1 horder
  exact (h.two_ends i x r hr hr1).trans
    (mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_left hpower (zero_le_one.trans h.two_ends_constant)) (by positivity))

theorem construct {k : ℕ} {m d d' pExp qExp : ℝ}
    (hbase : DiscreteEstimate (k+2) m d pExp)
    (hlift : DiscreteEstimate (k+3) d d' qExp)
    (hm : 0 ≤ m) (hpExp : 1 ≤ pExp) (hd : 0 ≤ d) (hqExp : 2 ≤ qExp)
    (hD : KakeyaScalar.pivotSet m d' < m+1)
    (width R c₀ C₀ B₀ K₀ xi₀ alpha beta bLog kLog xLog eps : ℝ)
    (hw : 0 ≤ width) (hc₀ : 0 < c₀) (hC₀ : 0 < C₀) (horder : c₀ ≤ C₀)
    (hB₀ : 0 < B₀) (hK₀ : 0 < K₀) (hxi₀ : 0 < xi₀)
    (ha : 0 < alpha) (ha1 : alpha ≤ 1/4) (hbeta : 0 < beta)
    (hbLog : 0 ≤ bLog) (hkLog : 0 ≤ kLog) (hxLog : 0 ≤ xLog) (heps : 0 < eps) :
    ∃ δ₀ : ℝ, 0 < δ₀ ∧ δ₀ ≤ 1 ∧ ∃ c : ℝ, 0 < c ∧
      ∀ {M : ℕ} (F : TubeFamily (k+2) M) (Full G : Fin M → Set (Space (k+2)))
      {δ lam xi B K A : ℝ},
      Input F Full G δ width R lam c₀ C₀ xi B alpha K beta →
      F.Separated δ → F.CapBound δ m A → 1 ≤ A → δ ≤ δ₀ →
      (1/δ)^(-(1:ℝ)/3) ≤ lam → xi ≤ 1 →
      B ≤ B₀*(Real.log (2/δ))^bLog → K ≤ K₀*(Real.log (2/δ))^kLog →
      xi₀*(Real.log (2/δ))^(-xLog) ≤ xi →
      c*A⁻¹*δ^(m-KakeyaScalar.pivotSet m d'+eps)*
        lam^(KakeyaScalar.pivotDensity pExp qExp)*(M:ℝ) ≤
          ((support F.tube Full δ width R).card:ℝ) := by
  let cLow := 1/(2*ratio c₀ C₀*SamplingMeasurableAssembly.highCoefficient (k+1))
  have hratio : 0 < ratio c₀ C₀ := div_pos hC₀ (lt_min hc₀ zero_lt_one)
  have hhigh : 0 < SamplingMeasurableAssembly.highCoefficient (k+1) := by
    unfold SamplingMeasurableAssembly.highCoefficient
    positivity
  have hcLow : 0 < cLow := by dsimp [cLow]; positivity
  have hC : 1 ≤ KakeyaScalar.pivotDensity pExp qExp := by
    unfold KakeyaScalar.pivotDensity
    linarith
  obtain ⟨cL,hcL,hlow⟩ := LowCellAbsorption.uniform_low_cap_bound hcLow hxi₀ hxLog hC hD heps.le
  obtain ⟨δ₀,hδ₀,hδ₀1,cP,hcP,hcases⟩ := SamplingMeasurablePivot.low_or_pivot
    hbase hlift hm hpExp hd hqExp width R c₀ C₀ B₀ K₀ xi₀ alpha beta bLog kLog xLog eps
    hw hc₀ hC₀ horder hB₀ hK₀ hxi₀ ha ha1 hbeta hbLog hkLog hxLog heps
  refine ⟨δ₀,hδ₀,hδ₀1,min cL cP,lt_min hcL hcP,?_⟩
  intro M F Full G δ lam xi B K A h hsep hcap hA hsmall hlam hxi1 hB hK hxi
  have hfactor : 0 ≤ A⁻¹*δ^(m-KakeyaScalar.pivotSet m d'+eps)*
      lam^(KakeyaScalar.pivotDensity pExp qExp)*(M:ℝ) := by
    positivity [h.scale_pos,h.density_pos]
  have hcases' := hcases F Full G h hsep hcap hA hsmall hlam hxi1 hB hK hxi
  rcases hcases' with hlo | hhi
  · have hlowForm : cLow*xi*lam*(M:ℝ)/(δ*Real.log (2/δ)) ≤
        ((support F.tube Full δ width R).card:ℝ) := by
      convert hlo using 1
      dsimp only [cLow,SamplingMeasurableAssembly.threshold]
      simp only [div_eq_mul_inv,mul_inv_rev,one_mul]
      ring
    have hbound := hlow h.scale_pos h.scale_le_one h.density_pos h.density_le_one
      (Nat.cast_nonneg M) hA hxi hlowForm
    have hmin := mul_le_mul_of_nonneg_right (min_le_left cL cP) hfactor
    calc
      _ ≤ cL*A⁻¹*δ^(m-KakeyaScalar.pivotSet m d'+eps)*
          lam^(KakeyaScalar.pivotDensity pExp qExp)*(M:ℝ) := by
        simpa only [mul_assoc] using hmin
      _ ≤ _ := hbound
  · have hmin := mul_le_mul_of_nonneg_right (min_le_right cL cP) hfactor
    calc
      _ ≤ cP*A⁻¹*δ^(m-KakeyaScalar.pivotSet m d'+eps)*
          lam^(KakeyaScalar.pivotDensity pExp qExp)*(M:ℝ) := by
        simpa only [mul_assoc] using hmin
      _ ≤ _ := hhi

/-- Every positive original two-ends exponent is allowed: its harmless
weakening to min(alpha,1/4) is performed before the uniform constants are chosen. -/
theorem all_exponents {k : ℕ} {m d d' pExp qExp : ℝ}
    (hbase : DiscreteEstimate (k+2) m d pExp)
    (hlift : DiscreteEstimate (k+3) d d' qExp)
    (hm : 0 ≤ m) (hpExp : 1 ≤ pExp) (hd : 0 ≤ d) (hqExp : 2 ≤ qExp)
    (hD : KakeyaScalar.pivotSet m d' < m+1)
    (width R c₀ C₀ B₀ K₀ xi₀ alpha beta bLog kLog xLog eps : ℝ)
    (hw : 0 ≤ width) (hc₀ : 0 < c₀) (hC₀ : 0 < C₀) (horder : c₀ ≤ C₀)
    (hB₀ : 0 < B₀) (hK₀ : 0 < K₀) (hxi₀ : 0 < xi₀)
    (ha : 0 < alpha) (hbeta : 0 < beta)
    (hbLog : 0 ≤ bLog) (hkLog : 0 ≤ kLog) (hxLog : 0 ≤ xLog) (heps : 0 < eps) :
    ∃ δ₀ : ℝ, 0 < δ₀ ∧ δ₀ ≤ 1 ∧ ∃ c : ℝ, 0 < c ∧
      ∀ {M : ℕ} (F : TubeFamily (k+2) M) (Full G : Fin M → Set (Space (k+2)))
      {δ lam xi B K A : ℝ},
      Input F Full G δ width R lam c₀ C₀ xi B alpha K beta →
      F.Separated δ → F.CapBound δ m A → 1 ≤ A → δ ≤ δ₀ →
      (1/δ)^(-(1:ℝ)/3) ≤ lam → xi ≤ 1 →
      B ≤ B₀*(Real.log (2/δ))^bLog → K ≤ K₀*(Real.log (2/δ))^kLog →
      xi₀*(Real.log (2/δ))^(-xLog) ≤ xi →
      c*A⁻¹*δ^(m-KakeyaScalar.pivotSet m d'+eps)*
        lam^(KakeyaScalar.pivotDensity pExp qExp)*(M:ℝ) ≤
          ((support F.tube Full δ width R).card:ℝ) := by
  have hamin : 0 < min alpha (1/4:ℝ) := lt_min ha (by norm_num)
  obtain ⟨δ₀,hδ₀,hδ₀1,c,hc,hbound⟩ := construct hbase hlift hm hpExp hd hqExp hD
    width R c₀ C₀ B₀ K₀ xi₀ (min alpha (1/4)) beta bLog kLog xLog eps
    hw hc₀ hC₀ horder hB₀ hK₀ hxi₀ hamin (min_le_right _ _) hbeta hbLog hkLog hxLog heps
  refine ⟨δ₀,hδ₀,hδ₀1,c,hc,?_⟩
  intro M F Full G δ lam xi B K A h hsep hcap hA hsmall hlam hxi1 hB hK hxi
  exact hbound F Full G (input_weaken_alpha h hamin.le (min_le_left _ _))
    hsep hcap hA hsmall hlam hxi1 hB hK hxi

end
end KakeyaFormal.SamplingHighDensity
