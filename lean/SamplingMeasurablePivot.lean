import SamplingMeasurableAssembly
import SampledMarkedEstimate

/-! Source measurable shadings construct their own sampling outcome and invoke
the actual marked pivot. No probability array, high set, narrow density band,
or good-outcome premise is supplied by the caller. The geometric conditioning
and its fixed logarithmic budgets remain explicit. -/
namespace KakeyaFormal.SamplingMeasurablePivot
open Finset SamplingNormalizedMeans SamplingSupport KakeyaSamplingApplication
open scoped BigOperators
noncomputable section
open Classical

/-- The radius's proved lower bound gives the inverse budget needed by pivot. -/
theorem inverse_log_budget {theta a L power : ℝ} (ha : 0 < a) (hL : 0 < L)
    (hbound : a*L^(-power) ≤ theta) : theta⁻¹ ≤ a⁻¹*L^power := by
  have hpos : 0 < a*L^(-power) := by positivity
  have hh := one_div_le_one_div_of_le hpos hbound
  have hpow : (L^(-power))⁻¹ = L^power := by rw [Real.rpow_neg hL.le,inv_inv]
  calc
    _ ≤ (a*L^(-power))⁻¹ := by simpa only [one_div] using hh
    _ = _ := by rw [mul_inv_rev,hpow]; ring

/-- On the original actual measurable input, either deterministic low cells
already have the explicit large population, or a constructed outcome proves
the pivot bound on the same available positive-measure support. Constants and
the sampling cutoff precede all configurations and all later coefficients. -/
theorem low_or_pivot {k : ℕ} {m d d' pExp qExp : ℝ}
    (hbase : DiscreteEstimate (k+2) m d pExp)
    (hlift : DiscreteEstimate (k+3) d d' qExp)
    (hm : 0 ≤ m) (hpExp : 1 ≤ pExp) (hd : 0 ≤ d) (hqExp : 2 ≤ qExp)
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
      let E := support F.tube Full δ width R
      (((1/ratio c₀ C₀)*(xi*lam*(M:ℝ)/δ))/(2*SamplingMeasurableAssembly.threshold (k+1) δ) ≤
        (E.card:ℝ)) ∨
      (c*A⁻¹*δ^(m-KakeyaScalar.pivotSet m d'+eps)*
        lam^(KakeyaScalar.pivotDensity pExp qExp)*(M:ℝ) ≤ (E.card:ℝ)) := by
  have heq : 0 < equalizer c₀ := lt_min hc₀ zero_lt_one
  have heq1 : equalizer c₀ ≤ 1 := min_le_right _ _
  have hratio1 : 1 ≤ ratio c₀ C₀ := by
    unfold ratio
    exact (le_div_iff₀ heq).mpr (by simpa only [one_mul,equalizer] using (min_le_left c₀ 1).trans horder)
  have hratio : 0 < ratio c₀ C₀ := zero_lt_one.trans_le hratio1
  have hball : 1 ≤ ballCoefficient (k+1) := by
    unfold ballCoefficient
    have hk := Nat.cast_nonneg (α:=ℝ) (k+1+1)
    linarith
  let theta₀ := SamplingTheta.choice (ratio c₀ C₀*K₀) beta
  have htheta₀ : 0 < theta₀ := SamplingTheta.choice_pos (mul_pos hratio hK₀)
  obtain ⟨c,hc,hcore⟩ := SampledMarkedEstimate.construct hbase hlift hm hpExp hd hqExp
    width R eps hw heps (equalizer c₀) (ratio c₀ C₀) (ballCoefficient (k+1))
    B₀ theta₀⁻¹ xi₀ alpha bLog (kLog/beta) xLog
    heq heq1 hratio1 hball hB₀ (inv_pos.mpr htheta₀) hxi₀ ha hbLog
    (div_nonneg hkLog hbeta.le) hxLog
  obtain ⟨δ₀,hδ₀,hδ₀1,hsample⟩ := SamplingMeasurableAssembly.construct (k+1)
    width R c₀ C₀ K₀ beta kLog hw hc₀ hC₀ hK₀ hbeta hkLog
  refine ⟨δ₀,hδ₀,hδ₀1,c,hc,?_⟩
  intro M F Full G δ lam xi B K A h hsep hcap hA hsmall hlam hxi1 hB hK hxi E
  obtain ⟨htheta,hbottomTheta,hupperTheta,hlowerTheta,hresult⟩ :=
    hsample F Full G h hsep hsmall hlam ha1 hK
  let theta := SamplingTheta.choice (ratio c₀ C₀*K) beta
  let p := SamplingNormalizedMeans.full F Full δ width R c₀ lam
  let q := SamplingNormalizedMeans.marked F Full G δ width R c₀ lam
  rcases hresult with hlo | hhigh
  · apply Or.inl
    have hcard : ((KakeyaSamplingDichotomy.low (markedMean q)
        (SamplingMeasurableAssembly.threshold (k+1) δ)).card:ℝ) ≤ E.card := by
      have hh := Finset.card_le_univ (KakeyaSamplingDichotomy.low (markedMean q)
        (SamplingMeasurableAssembly.threshold (k+1) δ))
      simpa only [Fintype.card_coe,E] using (Nat.cast_le (α:=ℝ)).mpr hh
    exact hlo.trans hcard
  · apply Or.inr
    obtain ⟨J,hbottom,hbottom2,hdepth,omega,hgood,hband⟩ := hhigh
    have hL : 0 < Real.log (2/δ) := Real.log_pos
      ((lt_div_iff₀ h.scale_pos).mpr (by linarith [h.scale_le_one]))
    have hthetaBudget : theta⁻¹ ≤ theta₀⁻¹*(Real.log (2/δ))^(kLog/beta) := by
      apply inverse_log_budget htheta₀ hL
      simpa only [neg_div] using hlowerTheta
    have hmarked : (1/ratio c₀ C₀)*(xi*lam*(M:ℝ)/δ) ≤ ∑ z, markedMean q z := by
      have hr : 1/ratio c₀ C₀ = equalizer c₀/C₀ := by unfold ratio; field_simp
      rw [hr]
      exact h.normalized_marked_mass
    have hband' : ∀ i, (2/3:ℝ)*(equalizer c₀*lam/δ) ≤ (fullShading omega i).card ∧
        ((fullShading omega i).card:ℝ) ≤ (4/3:ℝ)*(equalizer c₀*lam/δ) := by
      intro i
      simpa only [h.normalized_full_mean,commonMean] using hband i
    exact hcore F Full E h.scale_pos h.scale_le_one hA h.density_pos h.density_le_one
      h.marked_fraction_pos hxi1 h.count_pos h.two_ends_constant htheta
      (by linarith) hB hthetaBudget hxi hbottom2.le h.full_subset hsep h.bounded hcap
      p q (fun i z => (h.normalized_probabilities i z).1.trans (h.normalized_probabilities i z).2.1)
      h.normalized_full_le_weight
      (KakeyaSamplingDichotomy.high (markedMean q) (SamplingMeasurableAssembly.threshold (k+1) δ))
      omega hgood hband' hmarked

end
end KakeyaFormal.SamplingMeasurablePivot
