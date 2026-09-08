import AnisotropicDensityPower
import SamplingOriginalCells

/-! Uniform high-density estimates for the actual retained anisotropic
outputs, expressed in the original piece's density and population. The
selection's literal conditioning constants are bounded internally. -/
namespace KakeyaFormal.AnisotropicHighDensity
open Finset AnisotropicSamplingRetention AnisotropicSamplingBudgets
open TransformedGridSupport WidthNormalization GridShadingMeasure
noncomputable section

/-- The original measurable box data construct the output elsewhere. This
theorem applies the proved sampling pivot to that same output and recovers the
original density and population, absorbing every selection logarithm. -/
theorem original_parameters {k : ℕ} {m d d' pExp qExp : ℝ}
    (hbase : DiscreteEstimate (k+2) m d pExp)
    (hlift : DiscreteEstimate (k+3) d d' qExp)
    (hm : 0 ≤ m) (hpExp : 1 ≤ pExp) (hd : 0 ≤ d) (hqExp : 2 ≤ qExp)
    (hD : KakeyaScalar.pivotSet m d' < m+1)
    (width R angular e₀ B₀ K₀ alpha beta xLog bLog kLog eps : ℝ)
    (hw : 0 ≤ width) (hangular : 0 ≤ angular)
    (he₀ : 0 < e₀) (hB₀ : 0 < B₀) (hK₀ : 0 < K₀)
    (ha : 0 < alpha) (hbeta : 0 < beta)
    (hxLog : 0 ≤ xLog) (hbLog : 0 ≤ bLog) (hkLog : 0 ≤ kLog) (heps : 0 < eps) :
    ∃ δ₀ : ℝ, 0 < δ₀ ∧ δ₀ ≤ 1 ∧ ∃ c : ℝ, 0 < c ∧
      ∀ {M : ℕ} (Full : Fin M → Set (Space (k+2)))
      (u : Space (k+2)) (q : Cell (k+1)) (S : Finset (Cell (k+2)))
      {δ tau W lam e B K A : ℝ}
      (O : Output Full u q δ tau width R angular lam e B alpha beta K m A),
      0 < δ → 0 < tau → tau ≤ 1 → 1 ≤ W → 1 ≤ A →
      (∀ i, Full i ⊆ normalizedSet W (cellUnion δ S)) →
      δ/tau ≤ δ₀ → (1/(δ/tau))^(-(1:ℝ)/3) ≤ O.density →
      e₀*(Real.log (2/(δ/tau)))^(-xLog) ≤ e →
      B ≤ B₀*(Real.log (2/(δ/tau)))^bLog →
      K ≤ K₀*(Real.log (2/(δ/tau)))^kLog →
      c*A⁻¹*(δ/tau)^(m-KakeyaScalar.pivotSet m d'+eps)*
        lam^(KakeyaScalar.pivotDensity pExp qExp)*(M:ℝ) ≤ (S.card:ℝ) := by
  obtain ⟨Cdepth,xi₀,Bnew₀,Knew₀,hCdepth,hxi₀,hBnew₀,hKnew₀,hbudgets⟩ :=
    uniform_constants e₀ xLog angular beta B₀ K₀ bLog kLog
      he₀ hxLog hangular hB₀ hK₀
  obtain ⟨δs,hδs,hδs1,cS,hcS,hmain⟩ := SamplingOriginalCells.construct hbase hlift hm hpExp hd hqExp hD
    width R 2 4 Bnew₀ Knew₀ xi₀ alpha beta (bLog+xLog) (kLog+xLog+1) (xLog+1) (eps/2)
    hw (by norm_num) (by norm_num) (by norm_num) hBnew₀ hKnew₀ hxi₀ ha hbeta
    (by positivity) (by positivity) (by positivity) (by positivity)
  let C := KakeyaScalar.pivotDensity pExp qExp
  have hC : 1 ≤ C := by dsimp [C,KakeyaScalar.pivotDensity]; linarith
  let cRet := (e₀/4)^(C-1)*(e₀/(16*depthCoefficient e₀ xLog))
  have hcRet : 0 < cRet := by
    have := depthCoefficient_pos (e₀:=e₀) hxLog
    dsimp [cRet]
    positivity
  obtain ⟨ell,hell,hlogs⟩ := PivotLossAbsorption.inverse_log_delta
    (by have := mul_nonneg hxLog (by linarith : 0 ≤ C); linarith : 0 ≤ xLog*C+1)
    (by positivity : 0 < eps/2)
  refine ⟨min δs (2/Real.exp 1),lt_min hδs (by positivity),
    (min_le_left _ _).trans hδs1,cS*cRet*ell,by positivity,?_⟩
  intro M Full u q S δ tau W lam e B K A O hδ htau htau1 hW hA hFull
    hscale hhigh he hB hK
  let δ' := δ/tau
  let L := Real.log (2/δ')
  have hδ' : 0 < δ' := div_pos hδ htau
  have hδ'1 : δ' ≤ 1 := O.input.scale_le_one
  have hL : 1 ≤ L := by
    apply (Real.le_log_iff_exp_le (div_pos (by norm_num) hδ')).mpr
    apply (le_div_iff₀ hδ').mpr
    have hh : δ' ≤ 2/Real.exp 1 := hscale.trans (min_le_right _ _)
    simpa only [mul_comm] using (le_div_iff₀ (Real.exp_pos 1)).mp hh
  obtain ⟨_,hxi,hBnew,hKnew⟩ := hbudgets hL O.effective_pos he O.depth_bound hB hK
  have himage : ∀ i, O.full i ⊆ pieceMap u tau W q '' cellUnion δ S := by
    intro i z hz
    obtain ⟨y,hy,rfl⟩ := O.contained i hz
    obtain ⟨x,hx,rfl⟩ := hFull (O.index i) hy
    exact ⟨x,hx,rfl⟩
  have hbound := hmain O.family O.full O.marks u q S hδ htau htau1 hW himage O.input
    O.separated O.cap_bound hA (hscale.trans (min_le_left _ _)) hhigh O.xi_le_one hBnew hKnew hxi
  have hret := AnisotropicDensityPower.output_power O he₀ hxLog hL hC he
  have hret' := mul_le_mul_of_nonneg_left hret
    (by positivity : 0 ≤ cS*A⁻¹*δ'^(m-KakeyaScalar.pivotSet m d'+eps/2))
  have hmid : cS*A⁻¹*δ'^(m-KakeyaScalar.pivotSet m d'+eps/2)*
      (cRet*L^(-(xLog*C+1))*lam^C*(M:ℝ)) ≤ (S.card:ℝ) := by
    apply hret'.trans
    simpa only [C,δ',mul_assoc] using hbound
  have hlog := hlogs δ' hδ' hδ'1
  have hlam : 0 < lam := O.input.density_pos.trans_le O.density_upper
  have hsplit : δ'^(m-KakeyaScalar.pivotSet m d'+eps) =
      δ'^(m-KakeyaScalar.pivotSet m d'+eps/2)*δ'^(eps/2) := by
    rw [← Real.rpow_add hδ']
    congr 1
    ring
  calc
    _ = (cS*cRet*A⁻¹*δ'^(m-KakeyaScalar.pivotSet m d'+eps/2)*lam^C*(M:ℝ))*
        (ell*δ'^(eps/2)) := by rw [hsplit]; ring
    _ ≤ (cS*cRet*A⁻¹*δ'^(m-KakeyaScalar.pivotSet m d'+eps/2)*lam^C*(M:ℝ))*
        L^(-(xLog*C+1)) := mul_le_mul_of_nonneg_left hlog (by positivity)
    _ = cS*A⁻¹*δ'^(m-KakeyaScalar.pivotSet m d'+eps/2)*
        (cRet*L^(-(xLog*C+1))*lam^C*(M:ℝ)) := by ring
    _ ≤ _ := hmid

 /-- Upper conditioning budgets at the original mesh transfer across the
 complement of the coarse range with an explicit fixed coefficient. -/
theorem upper_log_transport {δ δ' a v v₀ b : ℝ}
    (hδ : 0 < δ) (hδ1 : δ ≤ 1) (hδ' : 0 < δ') (hδ'1 : δ' ≤ 1)
    (ha : 1 ≤ a) (hv₀ : 0 ≤ v₀) (hb : 0 ≤ b)
    (hscale : δ'^a ≤ δ) (hv : v ≤ v₀*(Real.log (2/δ))^b) :
    v ≤ (v₀*a^b)*(Real.log (2/δ'))^b := by
  have hL : 0 < Real.log (2/δ) :=
    Real.log_pos ((lt_div_iff₀ hδ).mpr (by linarith))
  have hL' : 0 < Real.log (2/δ') :=
    Real.log_pos ((lt_div_iff₀ hδ').mpr (by linarith))
  have hh := Real.rpow_le_rpow hL.le (LowCellAbsorption.log_scale_transport hδ hδ' ha hscale) hb
  have hmul := mul_le_mul_of_nonneg_left hh hv₀
  rw [Real.mul_rpow (by linarith : 0 ≤ a) hL'.le] at hmul
  exact hv.trans (by simpa only [mul_assoc] using hmul)

/-- Original-scale budgets suffice once the actual coarse-range complement
 has been supplied. The constants still precede both scales and every output. -/
theorem original_log_parameters {k : ℕ} {m d d' pExp qExp : ℝ}
    (hbase : DiscreteEstimate (k+2) m d pExp)
    (hlift : DiscreteEstimate (k+3) d d' qExp)
    (hm : 0 ≤ m) (hpExp : 1 ≤ pExp) (hd : 0 ≤ d) (hqExp : 2 ≤ qExp)
    (hD : KakeyaScalar.pivotSet m d' < m+1)
    (width R angular e₀ B₀ K₀ alpha beta xLog bLog kLog eps a : ℝ)
    (hw : 0 ≤ width) (hangular : 0 ≤ angular)
    (he₀ : 0 < e₀) (hB₀ : 0 < B₀) (hK₀ : 0 < K₀)
    (ha : 0 < alpha) (hbeta : 0 < beta) (haScale : 1 ≤ a)
    (hxLog : 0 ≤ xLog) (hbLog : 0 ≤ bLog) (hkLog : 0 ≤ kLog) (heps : 0 < eps) :
    ∃ δ₀ : ℝ, 0 < δ₀ ∧ δ₀ ≤ 1 ∧ ∃ c : ℝ, 0 < c ∧
      ∀ {M : ℕ} (Full : Fin M → Set (Space (k+2)))
      (u : Space (k+2)) (q : Cell (k+1)) (S : Finset (Cell (k+2)))
      {δ tau W lam e B K A : ℝ}
      (O : Output Full u q δ tau width R angular lam e B alpha beta K m A),
      0 < δ → 0 < tau → tau ≤ 1 → 1 ≤ W → 1 ≤ A →
      (∀ i, Full i ⊆ normalizedSet W (cellUnion δ S)) →
      δ/tau ≤ δ₀ → (δ/tau)^a ≤ δ →
      (1/(δ/tau))^(-(1:ℝ)/3) ≤ O.density →
      e₀*(Real.log (2/δ))^(-xLog) ≤ e →
      B ≤ B₀*(Real.log (2/δ))^bLog → K ≤ K₀*(Real.log (2/δ))^kLog →
      c*A⁻¹*(δ/tau)^(m-KakeyaScalar.pivotSet m d'+eps)*
        lam^(KakeyaScalar.pivotDensity pExp qExp)*(M:ℝ) ≤ (S.card:ℝ) := by
  have ha0 : 0 < a := zero_lt_one.trans_le haScale
  obtain ⟨δ₀,hδ₀,hδ₀1,c,hc,hmain⟩ := original_parameters hbase hlift hm hpExp hd hqExp hD
    width R angular (e₀*a^(-xLog)) (B₀*a^bLog) (K₀*a^kLog) alpha beta xLog bLog kLog eps
    hw hangular (by positivity) (by positivity) (by positivity) ha hbeta hxLog hbLog hkLog heps
  refine ⟨δ₀,hδ₀,hδ₀1,c,hc,?_⟩
  intro M Full u q S δ tau W lam e B K A O hδ htau htau1 hW hA hFull
    hscale hcompare hhigh he hB hK
  have hδ1 : δ ≤ 1 := ((div_le_one htau).mp O.input.scale_le_one).trans htau1
  have hδ' : 0 < δ/tau := O.input.scale_pos
  have hδ'1 : δ/tau ≤ 1 := O.input.scale_le_one
  exact hmain Full u q S O hδ htau htau1 hW hA hFull hscale hhigh
    (LowCellAbsorption.inverse_log_scale_transport hδ hδ1 hδ' hδ'1 haScale he₀ hxLog hcompare he)
    (upper_log_transport hδ hδ1 hδ' hδ'1 haScale hB₀.le hbLog hcompare hB)
    (upper_log_transport hδ hδ1 hδ' hδ'1 haScale hK₀.le hkLog hcompare hK)

end
end KakeyaFormal.AnisotropicHighDensity
