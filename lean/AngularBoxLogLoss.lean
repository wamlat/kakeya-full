import AngularBoxAlgebra
import HairbrushLogLoss

/-! Explicit logarithmic costs of actual angular-box segment/color/density
recovery, with constants fixed independently of density and both scales. -/
namespace KakeyaFormal.AngularBoxLogLoss
open AngularBoxRecovery AngularBoxAlgebra HairbrushScales HairbrushAllScales HairbrushLogLoss
open MeasureTheory
open scoped ENNReal BigOperators
noncomputable section
open Classical

theorem retention_log_lower (k : ℕ) {angular eta eta₀ L q : ℝ} (_hL : 0 < L)
    (hη : eta₀*L^(-q) ≤ eta) :
    retention k angular eta₀*L^(-q) ≤ retention k angular eta := by
  have hD : 0 ≤ (AnisotropicShading.segmentCount angular:ℝ)*
      (SeparationColoring.paletteSize (k+1) (1/directionLoss angular):ℝ) := by positivity
  have hh := div_le_div_of_nonneg_right hη hD
  unfold retention
  exact (by ring : eta₀/((AnisotropicShading.segmentCount angular:ℝ)*
      (SeparationColoring.paletteSize (k+1) (1/directionLoss angular):ℝ))*L^(-q) =
      (eta₀*L^(-q))/((AnisotropicShading.segmentCount angular:ℝ)*
      (SeparationColoring.paletteSize (k+1) (1/directionLoss angular):ℝ))).trans_le hh

/-- An upper logarithmic numerator and lower logarithmic denominator give
the explicit sum of exponents. -/
theorem quotient_log_upper {v v₀ e e₀ L b q : ℝ}
    (_hv : 0 ≤ v) (hv₀ : 0 < v₀) (he₀ : 0 < e₀) (hL : 0 < L)
    (hvbound : v ≤ v₀*L^b) (hebound : e₀*L^(-q) ≤ e) :
    v/e ≤ (v₀/e₀)*L^(b+q) := by
  have hh := div_le_div₀ (by positivity : 0 ≤ v₀*L^b) hvbound
    (by positivity : 0 < e₀*L^(-q)) hebound
  have hid : (v₀*L^b)/(e₀*L^(-q)) = (v₀/e₀)*L^(b+q) := by
    rw [show (v₀*L^b)/(e₀*L^(-q)) = (v₀/e₀)*(L^b/L^(-q)) by ring,
      ← Real.rpow_sub hL]
    congr 2
    ring
  exact hh.trans_eq hid

theorem endsCoefficient_log_upper (k : ℕ) {angular eta eta₀ B B₀ L b q : ℝ}
    (hB : 0 ≤ B) (hB₀ : 0 < B₀) (hη₀ : 0 < eta₀) (hL : 0 < L)
    (hBB : B ≤ B₀*L^b) (hη : eta₀*L^(-q) ≤ eta) :
    endsCoefficient k angular B eta ≤ endsCoefficient k angular B₀ eta₀*L^(b+q) := by
  have hh := quotient_log_upper hB hB₀ (retention_pos k (angular := angular) hη₀) hL hBB
    (retention_log_lower k hL hη)
  have hm := mul_le_mul_of_nonneg_left hh (by norm_num : (0:ℝ) ≤ 4)
  unfold endsCoefficient
  exact (by ring : B*(4/retention k angular eta) = 4*(B/retention k angular eta)).trans_le
    (hm.trans_eq (by ring))

theorem broadCoefficient_log_upper (k : ℕ) {angular eta eta₀ beta K K₀ L b q : ℝ}
    (ha : 0 ≤ angular) (hK : 0 ≤ K) (hK₀ : 0 < K₀) (hη₀ : 0 < eta₀) (hL : 0 < L)
    (hKK : K ≤ K₀*L^b) (hη : eta₀*L^(-q) ≤ eta) :
    broadCoefficient k angular beta K eta ≤ broadCoefficient k angular beta K₀ eta₀*L^(b+q) := by
  have hAng : 0 < angularLoss angular := lt_of_lt_of_le (by norm_num) (AngularBoxHairbrush.angularLoss_ge_one ha)
  have hpow : 0 < (angularLoss angular)^beta := Real.rpow_pos_of_pos hAng _
  have hbound : K*(angularLoss angular)^beta ≤ (K₀*(angularLoss angular)^beta)*L^b :=
    (mul_le_mul_of_nonneg_right hKK hpow.le).trans_eq (by ring)
  have hh := quotient_log_upper (mul_nonneg hK hpow.le) (mul_pos hK₀ hpow)
    (retention_pos k (angular := angular) hη₀) hL hbound (retention_log_lower k hL hη)
  have hm := mul_le_mul_of_nonneg_left hh (by norm_num : (0:ℝ) ≤ 8)
  unfold broadCoefficient
  exact (by ring : (K*(angularLoss angular)^beta)*(8/retention k angular eta) =
      8*((K*(angularLoss angular)^beta)/retention k angular eta)).trans_le
    (hm.trans_eq (by ring))

def logarithmicLoss (k : ℕ) (alpha beta b c q : ℝ) : ℝ :=
  HairbrushLogLoss.lossPower k alpha beta (b+q) (c+q)+(5/2)*q

def logarithmicConstant (k : ℕ) (angular eta₀ alpha beta B₀ K₀ m A : ℝ) : ℝ :=
  radiusConstant k (endsCoefficient k angular B₀ eta₀) (broadCoefficient k angular beta K₀ eta₀) alpha beta*
    (retention k angular eta₀)^((5:ℝ)/2)/
      (16*allScaleConstant k*Real.sqrt (capCoefficient k angular m A))

theorem logarithmicLoss_formula (k : ℕ) (alpha beta b c q : ℝ) :
    logarithmicLoss k alpha beta b c q =
      (k+1:ℕ)*(b/alpha+c/beta)+q*((k+1:ℕ)*(1/alpha+1/beta)+5/2)+5/2 := by
  unfold logarithmicLoss lossPower
  ring

theorem logarithmicLoss_nonneg (k : ℕ) {alpha beta b c q : ℝ}
    (ha : 0 < alpha) (hb : 0 < beta) (hb₀ : 0 ≤ b) (hc : 0 ≤ c) (hq : 0 ≤ q) :
    0 ≤ logarithmicLoss k alpha beta b c q := by
  rw [logarithmicLoss_formula]
  positivity

theorem logarithmicConstant_pos (k : ℕ) {angular eta₀ alpha beta B₀ K₀ m A : ℝ}
    (ha : 0 ≤ angular) (hη₀ : 0 < eta₀) (hB₀ : 0 < B₀) (hK₀ : 0 < K₀)
    (hCap : 0 < capCoefficient k angular m A) :
    0 < logarithmicConstant k angular eta₀ alpha beta B₀ K₀ m A := by
  have he₀ := retention_pos k (angular := angular) hη₀
  have hAng : 0 < angularLoss angular := lt_of_lt_of_le (by norm_num) (AngularBoxHairbrush.angularLoss_ge_one ha)
  have hB : 0 < endsCoefficient k angular B₀ eta₀ := by unfold endsCoefficient; positivity
  have hK : 0 < broadCoefficient k angular beta K₀ eta₀ := by unfold broadCoefficient; positivity
  have hR := radiusConstant_pos k (alpha := alpha) (beta := beta) hB hK
  have hC := allScaleConstant_pos k
  unfold logarithmicConstant
  positivity

/-- The full one-box prefactor has an explicit polynomial logarithmic loss.
In particular, the loss exponent is independent of shading density. -/
theorem density_prefactor_log_lower {k : ℕ} {δ angular eta eta₀ alpha beta B K B₀ K₀ m A L b c q : ℝ}
    (hδ : 0 < δ) (hδ1 : δ ≤ 1) (ha : 0 ≤ angular) (hη : 0 < eta) (hη₀ : 0 < eta₀)
    (halpha : 0 < alpha) (hbeta : 0 < beta) (hB : 0 < B) (hK : 0 < K)
    (hB₀ : 0 < B₀) (hK₀ : 0 < K₀) (hCap : 0 < capCoefficient k angular m A) (hL : 0 < L)
    (hBB : B ≤ B₀*L^b) (hKK : K ≤ K₀*L^c) (hηbound : eta₀*L^(-q) ≤ eta)
    (hlog : hairbrushLog k δ ≤ logCoefficient k*L) :
    logarithmicConstant k angular eta₀ alpha beta B₀ K₀ m A*L^(-logarithmicLoss k alpha beta b c q) ≤
      densityConstant k angular eta alpha beta B K m A/(hairbrushLog k δ)^((5:ℝ)/2) := by
  have he := retention_pos k (angular := angular) hη
  have he₀ := retention_pos k (angular := angular) hη₀
  have hAng : 0 < angularLoss angular := lt_of_lt_of_le (by norm_num) (AngularBoxHairbrush.angularLoss_ge_one ha)
  have hBr : 0 < endsCoefficient k angular B eta := by unfold endsCoefficient; positivity
  have hKr : 0 < broadCoefficient k angular beta K eta := by unfold broadCoefficient; positivity
  have hBr₀ : 0 < endsCoefficient k angular B₀ eta₀ := by unfold endsCoefficient; positivity
  have hKr₀ : 0 < broadCoefficient k angular beta K₀ eta₀ := by unfold broadCoefficient; positivity
  have hpref := hairbrush_prefactor_log_lower hδ hδ1 hBr hKr hBr₀ hKr₀ halpha hbeta hL
    (endsCoefficient_log_upper k hB.le hB₀ hη₀ hL hBB hηbound)
    (broadCoefficient_log_upper k ha hK.le hK₀ hη₀ hL hKK hηbound) hlog
  have hepow := Real.rpow_le_rpow
    (by positivity : 0 ≤ retention k angular eta₀*L^(-q)) (retention_log_lower k hL hηbound)
    (by norm_num : (0:ℝ) ≤ 5/2)
  have hpowid : (retention k angular eta₀*L^(-q))^((5:ℝ)/2) =
      (retention k angular eta₀)^((5:ℝ)/2)*L^(-(5/2)*q) := by
    rw [Real.mul_rpow he₀.le (Real.rpow_nonneg hL.le _),← Real.rpow_mul hL.le]
    congr 2
    ring
  rw [hpowid] at hepow
  have hR : 0 ≤ (concentrationRadius (endsCoefficient k angular B eta) alpha*
      concentrationRadius (broadCoefficient k angular beta K eta) beta)^(k+1)/(hairbrushLog k δ)^((5:ℝ)/2) := by
    have hR₁ := concentrationRadius_pos (alpha := alpha) hBr
    have hR₂ := concentrationRadius_pos (alpha := beta) hKr
    have hLog := hairbrushLog_pos (k := k) hδ hδ1
    positivity
  have hm := mul_le_mul hpref hepow (by positivity) hR
  have hC := allScaleConstant_pos k
  have hden : 0 < 16*allScaleConstant k*Real.sqrt (capCoefficient k angular m A) := by positivity
  have hh := div_le_div_of_nonneg_right hm hden.le
  have hleft :
      (radiusConstant k (endsCoefficient k angular B₀ eta₀) (broadCoefficient k angular beta K₀ eta₀) alpha beta*
        L^(-lossPower k alpha beta (b+q) (c+q)))*
        ((retention k angular eta₀)^((5:ℝ)/2)*L^(-(5/2)*q))/
          (16*allScaleConstant k*Real.sqrt (capCoefficient k angular m A)) =
      logarithmicConstant k angular eta₀ alpha beta B₀ K₀ m A*L^(-logarithmicLoss k alpha beta b c q) := by
    rw [show -(5/2)*q = -((5/2)*q) by ring]
    unfold logarithmicConstant logarithmicLoss
    rw [show -(lossPower k alpha beta (b+q) (c+q)+(5/2)*q) =
      -lossPower k alpha beta (b+q) (c+q)+ -((5/2)*q) by ring,Real.rpow_add hL]
    ring
  rw [hleft] at hh
  exact hh.trans_eq (by unfold densityConstant; ring)

/-- The original physical-scale logarithm controls every angularly enlarged
scale, so no angular-scale logarithmic loss remains unbudgeted. -/
theorem angular_prefactor_log_lower {k : ℕ} {δ tau angular eta eta₀ alpha beta B K B₀ K₀ m A L b c q : ℝ}
    (hδ : 0 < δ) (hδtau : δ ≤ tau) (htau1 : tau ≤ 1)
    (ha : 0 ≤ angular) (hη : 0 < eta) (hη₀ : 0 < eta₀)
    (halpha : 0 < alpha) (hbeta : 0 < beta) (hB : 0 < B) (hK : 0 < K)
    (hB₀ : 0 < B₀) (hK₀ : 0 < K₀) (hCap : 0 < capCoefficient k angular m A) (hL : 0 < L)
    (hBB : B ≤ B₀*L^b) (hKK : K ≤ K₀*L^c) (hηbound : eta₀*L^(-q) ≤ eta)
    (hlog : hairbrushLog k δ ≤ logCoefficient k*L) :
    logarithmicConstant k angular eta₀ alpha beta B₀ K₀ m A*L^(-logarithmicLoss k alpha beta b c q) ≤
      densityConstant k angular eta alpha beta B K m A/(hairbrushLog k (δ/tau))^((5:ℝ)/2) := by
  have htau : 0 < tau := hδ.trans_le hδtau
  have hδnew : δ ≤ δ/tau := (le_div_iff₀ htau).mpr (by nlinarith)
  exact density_prefactor_log_lower (div_pos hδ htau) ((div_le_one htau).mpr hδtau)
    ha hη hη₀ halpha hbeta hB hK hB₀ hK₀ hCap hL hBB hKK hηbound
    ((hairbrushLog_mono_width hδ hδnew).trans hlog)

/-- Fully constructed actual one-box bound with every logarithmic loss
expressed using the original physical scale. -/
theorem single_box_logarithmic {k M : ℕ} (F : TubeFamily (k+2) M)
    (Full Ref : Fin M → Set (Space (k+2))) (u : Space (k+2)) (label : Cell (k+1))
    {δ tau angular eta eta₀ lam alpha beta B K B₀ K₀ m A L b c q : ℝ}
    (hM : 0 < M) (hu : ‖u‖ = 1) (hδ : 0 < δ) (hδtau : δ ≤ tau) (htau1 : tau ≤ 1)
    (ha : 0 ≤ angular) (hη : 0 < eta) (hη1 : eta ≤ 1) (hlam : 0 < lam) (hlam1 : lam ≤ 1)
    (hB : 1 ≤ B) (halpha : 0 < alpha) (hK : 1 ≤ K) (hbeta : 0 < beta) (hm : 1 ≤ m) (hA : 1 ≤ A)
    (hFull : ∀ i, MeasurableSet (Full i)) (hRef : ∀ i, MeasurableSet (Ref i))
    (hRefFull : ∀ i, Ref i ⊆ Full i) (hsub : ∀ i, Full i ⊆ (F.tube i).carrier δ)
    (hlocal : ∀ i, projectiveDistance (F.tube i).direction u ≤ angular*tau)
    (hsep : F.Separated δ) (hcap : F.CapBound δ m A)
    (hupper : ∀ i, (volume : Measure (Space (k+2))).real (Full i) ≤ 2*lam*δ^(k+1))
    (hmass : eta*lam*δ^(k+1)*(M:ℝ) ≤ ∑ i, (volume : Measure (Space (k+2))).real (Ref i))
    (hbroad : ∀ x, AngularDecomposition.Broad F (Finset.univ.filter (fun i => x ∈ Ref i)) δ beta tau K)
    (hends : ∀ i p r, δ ≤ r → r ≤ 1 → (volume : Measure (Space (k+2))).real (Full i ∩ Metric.closedBall p r) ≤
      B*r^alpha*(volume : Measure (Space (k+2))).real (Full i))
    (hη₀ : 0 < eta₀) (hB₀ : 0 < B₀) (hK₀ : 0 < K₀) (hL : 0 < L)
    (hBB : B ≤ B₀*L^b) (hKK : K ≤ K₀*L^c) (hηbound : eta₀*L^(-q) ≤ eta)
    (hlog : hairbrushLog k δ ≤ logCoefficient k*L) :
    logarithmicConstant k angular eta₀ alpha beta B₀ K₀ m A*L^(-logarithmicLoss k alpha beta b c q)*
      lam^2*(M:ℝ)*δ^(k+1)*(δ/tau)^((m-1)/2) ≤ (volume : Measure (Space (k+2))).real (⋃ i, Ref i) := by
  have hmain := single_box_quadratic_density F Full Ref u label hM hu hδ hδtau htau1 ha hη hη1 hlam hlam1
    hB halpha hK hbeta hm hA hFull hRef hRefFull hsub hlocal hsep hcap hupper hmass hbroad hends
  have hCap : 0 < capCoefficient k angular m A := lt_of_lt_of_le (by norm_num)
    (AngularBoxHairbrush.capCoefficient_ge_one k ha (by linarith) hA)
  have hpre := angular_prefactor_log_lower hδ hδtau htau1 ha hη hη₀ halpha hbeta
    (by linarith : 0 < B) (by linarith : 0 < K) hB₀ hK₀ hCap hL hBB hKK hηbound hlog
  have htau : 0 < tau := hδ.trans_le hδtau
  have hfac : 0 ≤ lam^2*(M:ℝ)*δ^(k+1)*(δ/tau)^((m-1)/2) := by positivity
  have hh := mul_le_mul_of_nonneg_right hpre hfac
  have hid₁ :
      (logarithmicConstant k angular eta₀ alpha beta B₀ K₀ m A*L^(-logarithmicLoss k alpha beta b c q))*
        (lam^2*(M:ℝ)*δ^(k+1)*(δ/tau)^((m-1)/2)) =
      logarithmicConstant k angular eta₀ alpha beta B₀ K₀ m A*L^(-logarithmicLoss k alpha beta b c q)*
        lam^2*(M:ℝ)*δ^(k+1)*(δ/tau)^((m-1)/2) := by ring
  have hid₂ :
      (densityConstant k angular eta alpha beta B K m A/(hairbrushLog k (δ/tau))^((5:ℝ)/2))*
        (lam^2*(M:ℝ)*δ^(k+1)*(δ/tau)^((m-1)/2)) =
      densityConstant k angular eta alpha beta B K m A*lam^2*(M:ℝ)*δ^(k+1)*(δ/tau)^((m-1)/2)/
        (hairbrushLog k (δ/tau))^((5:ℝ)/2) := by ring
  rw [hid₁,hid₂] at hh
  exact hh.trans hmain

end
end KakeyaFormal.AngularBoxLogLoss

#print axioms KakeyaFormal.AngularBoxLogLoss.density_prefactor_log_lower
#print axioms KakeyaFormal.AngularBoxLogLoss.single_box_logarithmic
