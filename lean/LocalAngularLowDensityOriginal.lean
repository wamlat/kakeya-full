import LocalAngularLowDensity
import AnisotropicDensityPower

/-! The original-density and original-population form of the proved local
low-density case. All conditioning is given in the original natural logarithm;
using the proved seedLog comparison avoids an unnecessary small-scale cutoff. -/
namespace KakeyaFormal.LocalAngularLowDensityOriginal
open MeasureTheory LocalAngularLowDensity AngularSeedLogLoss WidthNormalization
open scoped BigOperators ENNReal
noncomputable section
open Classical

/-- Actual retained density and population are converted back to the original
box parameters, with epsilon split between the geometric bound and the actual
selection loss. No density-power/population estimate is assumed. -/
theorem original_parameters (k : ℕ)
    {angular eta₀ alpha beta B₀ K₀ bLog kLog qLog a m D C eps e₀ xLog : ℝ}
    (ha : 0 ≤ angular) (heta₀ : 0 < eta₀) (halpha : 0 < alpha) (hbeta : 0 < beta)
    (hB₀ : 0 < B₀) (hK₀ : 0 < K₀) (hbLog : 0 ≤ bLog) (hkLog : 0 ≤ kLog)
    (hqLog : 0 ≤ qLog) (he₀ : 0 < e₀) (hxLog : 0 ≤ xLog) (haScale : 1 ≤ a) (hm : 1 ≤ m) (hC : 2 ≤ C) (heps : 0 < eps)
    (hmargin : 0 < (m+3)/2-D+(C-2)/3) :
    ∃ c : ℝ, 0 < c ∧ ∀ {M : ℕ} (F : TubeFamily (k+2) M)
      (Full Ref : Fin M → Set (Space (k+2))) (u : Space (k+2)) (label : Cell (k+1))
      (S : Finset (Cell (k+2))) {δ tau eta lam B K A W R e Anew : ℝ},
      0 < M → ‖u‖=1 → 0 < δ → δ ≤ tau → tau ≤ 1 → 0 < eta → eta ≤ 1 →
      0 < lam → lam ≤ 1 → 1 ≤ B → 1 ≤ K → 1 ≤ A → 1 ≤ W →
      (δ/tau)^a ≤ δ →
      (∀ i, MeasurableSet (Full i)) → (∀ i, MeasurableSet (Ref i)) →
      (∀ i, Ref i ⊆ Full i) → (∀ i, Full i ⊆ (F.tube i).carrier δ) →
      (∀ i, projectiveDistance (F.tube i).direction u ≤ angular*tau) →
      F.Separated δ → F.CapBound δ m A →
      (∀ i, (volume : Measure (Space (k+2))).real (Full i) ≤ 2*lam*δ^(k+1)) →
      eta*lam*δ^(k+1)*(M:ℝ) ≤ ∑ i, (volume : Measure (Space (k+2))).real (Ref i) →
      (∀ x, AngularDecomposition.Broad F (Finset.univ.filter (fun i => x ∈ Ref i)) δ beta tau K) →
      (∀ i x r, δ ≤ r → r ≤ 1 →
        (volume : Measure (Space (k+2))).real (Full i ∩ Metric.closedBall x r) ≤
          B*r^alpha*(volume : Measure (Space (k+2))).real (Full i)) →
      B ≤ B₀*(Real.log (2/δ))^bLog → K ≤ K₀*(Real.log (2/δ))^kLog →
      eta₀*(Real.log (2/δ))^(-qLog) ≤ eta →
      (⋃ i, Full i) ⊆ normalizedSet W (GridShadingMeasure.cellUnion δ S) →
      ∀ O : AnisotropicSamplingRetention.Output Full u label δ tau 1 R angular lam e B alpha beta K m Anew,
      O.density ≤ (δ/tau)^((1:ℝ)/3) → e₀*(Real.log (2/δ))^(-xLog) ≤ e →
      c*A⁻¹*(δ/tau)^(m-D+eps)*lam^C*(M:ℝ) ≤ (S.card:ℝ) := by
  obtain ⟨cS,hcS,hmain⟩ := retained_low_density k ha heta₀ halpha hbeta hB₀ hK₀
    hbLog hkLog hqLog haScale hm hC (by positivity : 0 ≤ eps/2) hmargin
  let cRet := (e₀/4)^(C-1)*(e₀/(16*AnisotropicSamplingBudgets.depthCoefficient e₀ xLog))
  have hcRet : 0 < cRet := by
    have := AnisotropicSamplingBudgets.depthCoefficient_pos (e₀:=e₀) hxLog
    dsimp [cRet]
    positivity
  have hpower : 0 ≤ xLog*C+1 := by nlinarith
  obtain ⟨ell,hell,hlogs⟩ := inverse_seedLog_uniform hpower (by positivity : 0 < eps/2) haScale
  refine ⟨cS*cRet*ell,by positivity,?_⟩
  intro M F Full Ref u label S δ tau eta lam B K A W R e Anew hM hu hδ hδtau htau1
    heta heta1 hlam hlam1 hB hK hA hW hscale hFull hRef hRefFull hsub hlocal hsep hcap
    hupper hmass hbroad hends hBB hKK hetabudget hsupport O hsmall hebudget
  have htau : 0 < tau := hδ.trans_le hδtau
  have hδ1 : δ ≤ 1 := hδtau.trans htau1
  have hs : 0 < δ/tau := div_pos hδ htau
  have hs1 : δ/tau ≤ 1 := (div_le_one htau).mpr hδtau
  have hLn : 0 < Real.log (2/δ) := Real.log_pos ((lt_div_iff₀ hδ).mpr (by linarith))
  have he : e₀*(seedLog δ)^(-xLog) ≤ e :=
    (mul_le_mul_of_nonneg_left
      (Real.rpow_le_rpow_of_nonpos hLn (natural_le_seedLog hδ hδ1) (by linarith)) he₀.le).trans hebudget
  have hbound := hmain F Full Ref u label S hM hu hδ hδtau htau1 heta heta1 hlam hlam1 hB hK hA hW
    hscale hFull hRef hRefFull hsub hlocal hsep hcap hupper hmass hbroad hends hBB hKK hetabudget hsupport O hsmall
  have hret := AnisotropicDensityPower.output_power O he₀ hxLog (seedLog_ge_one hδ hδ1) (by linarith : 1 ≤ C) he
  have hret' := mul_le_mul_of_nonneg_left hret
    (by positivity : 0 ≤ cS*A⁻¹*(δ/tau)^(m-D+eps/2))
  have hmid : cS*A⁻¹*(δ/tau)^(m-D+eps/2)*
      (cRet*(seedLog δ)^(-(xLog*C+1))*lam^C*(M:ℝ)) ≤ (S.card:ℝ) := by
    apply hret'.trans
    simpa only [mul_assoc] using hbound
  have hlog := hlogs hδ hδ1 hs hs1 hscale
  have hsplit : (δ/tau)^(m-D+eps) = (δ/tau)^(m-D+eps/2)*(δ/tau)^(eps/2) := by
    rw [← Real.rpow_add hs]
    congr 1
    ring
  calc
    _ = (cS*cRet*A⁻¹*(δ/tau)^(m-D+eps/2)*lam^C*(M:ℝ))*(ell*(δ/tau)^(eps/2)) := by
      rw [hsplit]
      ring
    _ ≤ (cS*cRet*A⁻¹*(δ/tau)^(m-D+eps/2)*lam^C*(M:ℝ))*(seedLog δ)^(-(xLog*C+1)) :=
      mul_le_mul_of_nonneg_left hlog (by positivity)
    _ = cS*A⁻¹*(δ/tau)^(m-D+eps/2)*(cRet*(seedLog δ)^(-(xLog*C+1))*lam^C*(M:ℝ)) := by ring
    _ ≤ _ := hmid

end
end KakeyaFormal.LocalAngularLowDensityOriginal
