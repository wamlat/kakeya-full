import AngularSeedSqrtCap

/-! Uniform logarithmic constants for actual measurable angular pieces.
Only the actual depth and common scale enter this algebraic interface. -/
namespace KakeyaFormal.MeasurableSeedLogLoss
open AngularSeedPieces AngularSeedHairbrush AngularSeedLogLoss
open AngularBoxAlgebra AngularBoxLogLoss AngularBoxRecovery HairbrushScales
noncomputable section

/-- Actual finite depth is controlled independently of the nature of atoms. -/
theorem depth_budget (J : ℕ) {δ : ℝ} (hδ : 0 < δ)
    (hdepth : (J:ℝ) ≤ Real.log (1/δ)/Real.log 2) : (J:ℝ)+1 ≤ seedLog δ := by
  rw [seedLog_identity hδ]
  linarith

theorem rate_budget (k J : ℕ) {δ : ℝ} (hδ : 0 < δ) (_hδ1 : δ ≤ 1)
    (hdepth : (J:ℝ) ≤ Real.log (1/δ)/Real.log 2) :
    rateBase k*(seedLog δ)^(-(1:ℝ)) ≤ retentionRate k J := by
  have hJ : 0 < (J:ℝ)+1 := by positivity
  have hh := one_div_le_one_div_of_le hJ (depth_budget J hδ hdepth)
  have hm := mul_le_mul_of_nonneg_left hh (rateBase_pos k).le
  calc
    _ = rateBase k*(1/seedLog δ) := by rw [Real.rpow_neg_one]; ring
    _ ≤ rateBase k*(1/((J:ℝ)+1)) := hm
    _ = _ := by
      unfold rateBase retentionRate
      simp only [div_eq_mul_inv,mul_inv_rev]
      ring

theorem eta_budget (k J : ℕ) {δ : ℝ} (hδ : 0 < δ) (hδ1 : δ ≤ 1)
    (hdepth : (J:ℝ) ≤ Real.log (1/δ)/Real.log 2) :
    etaBase k*(seedLog δ)^(-(1:ℝ)) ≤ retentionRate k J/4 := by
  have hh := div_le_div_of_nonneg_right (rate_budget k J hδ hδ1 hdepth) (by norm_num : (0:ℝ) ≤ 4)
  simpa only [etaBase,div_mul_eq_mul_div] using hh

/-- Actual one-box constant with original physical full two-ends coefficient B.
No grid width or artificial full-cell realization enters this coefficient. -/
def depthConstant (k J : ℕ) (alpha beta B m A : ℝ) : ℝ :=
  densityConstant k 3 (retentionRate (k+1) J/4) alpha beta B
    (broadConstant (k+1) beta) m A

def uniformConstant (k : ℕ) (alpha beta B₀ m : ℝ) : ℝ :=
  logarithmicConstant k 3 (etaBase (k+1)) alpha beta B₀
    (broadConstant (k+1) beta) m 1*(3*rateBase (k+1)/16)

theorem depthConstant_pos (k J : ℕ) {alpha beta B m A : ℝ}
    (hbeta : 0 < beta) (hB : 1 ≤ B) (hA : 1 ≤ A) :
    0 < depthConstant k J alpha beta B m A := by
  exact densityConstant_pos k (by norm_num) (div_pos (retentionRate_pos _ _) (by norm_num))
    (zero_lt_one.trans_le hB) (zero_lt_one.trans_le (broadConstant_ge_one _ hbeta.le))
    (zero_lt_one.trans_le hA)

theorem uniformConstant_pos (k : ℕ) {alpha beta B₀ m : ℝ}
    (hbeta : 0 < beta) (hB₀ : 1 ≤ B₀) (hm : 1 ≤ m) :
    0 < uniformConstant k alpha beta B₀ m := by
  have hh := logarithmicConstant_pos k (alpha:=alpha) (beta:=beta)
    (by norm_num : (0:ℝ) ≤ 3) (etaBase_pos (k+1)) (zero_lt_one.trans_le hB₀)
    (zero_lt_one.trans_le (broadConstant_ge_one (k+1) hbeta.le))
    (zero_lt_one.trans_le (AngularBoxHairbrush.capCoefficient_ge_one k (by norm_num)
      (by linarith : 0 ≤ m) (by norm_num : (1:ℝ) ≤ 1)))
  unfold uniformConstant
  positivity [rateBase_pos (k+1)]

/-- Exact square-root-cap extraction with all remaining scale/depth loss
uniformly bounded by a fixed logarithmic power. -/
theorem uniform_prefactor (k J : ℕ) {δ tau alpha beta B B₀ b m A : ℝ}
    (hδ : 0 < δ) (hlo : δ ≤ tau) (hhi : tau ≤ 1)
    (hdepth : (J:ℝ) ≤ Real.log (1/δ)/Real.log 2)
    (halpha : 0 < alpha) (hbeta : 0 < beta)
    (hB : 1 ≤ B) (hB₀ : 1 ≤ B₀) (hm : 1 ≤ m) (hA : 1 ≤ A)
    (hBB : B ≤ B₀*(seedLog δ)^b) :
    uniformConstant k alpha beta B₀ m/Real.sqrt A*(seedLog δ)^(-uniformLoss k alpha beta b) ≤
      (depthConstant k J alpha beta B m A*(3*retentionRate (k+1) J/16))/
        (hairbrushLog k (δ/tau))^((5:ℝ)/2) := by
  have hδ1 := hlo.trans hhi
  have hL : 0 < seedLog δ := zero_lt_one.trans_le (seedLog_ge_one hδ hδ1)
  have htau := hδ.trans_le hlo
  have hBroad := zero_lt_one.trans_le (broadConstant_ge_one (k+1) hbeta.le)
  have hCap := zero_lt_one.trans_le (AngularBoxHairbrush.capCoefficient_ge_one k
    (by norm_num : (0:ℝ) ≤ 3) (by linarith : 0 ≤ m) hA)
  have hη : 0 < retentionRate (k+1) J/4 := by positivity [retentionRate_pos (k+1) J]
  have hp := angular_prefactor_log_lower hδ hlo hhi (by norm_num : (0:ℝ) ≤ 3)
    hη (etaBase_pos (k+1)) halpha hbeta (zero_lt_one.trans_le hB) hBroad
    (zero_lt_one.trans_le hB₀) hBroad hCap hL hBB
    (by simp : broadConstant (k+1) beta ≤ broadConstant (k+1) beta*(seedLog δ)^(0:ℝ))
    (eta_budget (k+1) J hδ hδ1 hdepth) (le_refl (hairbrushLog k δ))
  rw [logarithmicConstant_cap_identity k (by linarith : 0 ≤ A)] at hp
  have hr := rate_budget (k+1) J hδ hδ1 hdepth
  have hf : (3*rateBase (k+1)/16)*(seedLog δ)^(-(1:ℝ)) ≤
      3*retentionRate (k+1) J/16 := by
    have hh := mul_le_mul_of_nonneg_left hr (by norm_num : (0:ℝ) ≤ 3/16)
    convert hh using 1 <;> first | rfl | ring
  have hlog := hairbrushLog_pos (k:=k) (div_pos hδ htau) ((div_le_one htau).mpr hlo)
  have hseed := depthConstant_pos k J (alpha:=alpha) (m:=m) hbeta hB hA
  have hmul := mul_le_mul hp hf (by positivity [rateBase_pos (k+1)]) (by
    change 0 ≤ depthConstant k J alpha beta B m A/(hairbrushLog k (δ/tau))^((5:ℝ)/2)
    positivity)
  calc
    _ = (logarithmicConstant k 3 (etaBase (k+1)) alpha beta B₀
        (broadConstant (k+1) beta) m 1/Real.sqrt A*(seedLog δ)^(-logarithmicLoss k alpha beta b 0 1))*
        ((3*rateBase (k+1)/16)*(seedLog δ)^(-(1:ℝ))) := by
      unfold uniformConstant uniformLoss
      rw [show -(logarithmicLoss k alpha beta b 0 1+1) =
        -logarithmicLoss k alpha beta b 0 1+ -(1:ℝ) by ring,Real.rpow_add hL]
      ring
    _ ≤ _ := hmul.trans_eq (by unfold depthConstant; ring)

end
end KakeyaFormal.MeasurableSeedLogLoss
