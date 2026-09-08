import AngularSeedBound
import AngularBoxLogLoss
import LogLoss

/-! Uniform scale-independent logarithmic budgets for the actual finite seed.
The cap loss is extracted explicitly, so constants do not depend on A. -/
namespace KakeyaFormal.AngularSeedLogLoss
open AngularSeedPieces AngularSeedRealization AngularSeedHairbrush AngularSeedBound
open AngularBoxAlgebra AngularBoxLogLoss AngularBoxRecovery HairbrushScales WidthNormalization
noncomputable section

/-- A single logarithm controls both the actual angular depth and hairbrush. -/
def seedLog (δ : ℝ) : ℝ := Real.logb 2 (2/δ)+2

theorem seedLog_ge_one {δ : ℝ} (hδ : 0 < δ) (hδ1 : δ ≤ 1) : 1 ≤ seedLog δ := by
  have hh := Real.logb_nonneg (by norm_num : (1:ℝ) < 2)
    ((le_div_iff₀ hδ).mpr (by linarith) : (1:ℝ) ≤ 2/δ)
  unfold seedLog
  linarith

theorem seedLog_identity {δ : ℝ} (hδ : 0 < δ) :
    seedLog δ = Real.log (1/δ)/Real.log 2+3 := by
  unfold seedLog Real.logb
  rw [Real.log_div (by norm_num : (2:ℝ) ≠ 0) hδ.ne',Real.log_div one_ne_zero hδ.ne',Real.log_one]
  have hlog : Real.log (2:ℝ) ≠ 0 := (Real.log_pos (by norm_num)).ne'
  field_simp
  ring

theorem depth_budget {k M : ℕ} {F : TubeFamily (k+1) M} {δ beta : ℝ}
    (P : Pieces F δ beta) (hδ : 0 < δ) : (P.J:ℝ)+1 ≤ seedLog δ := by
  rw [seedLog_identity hδ]
  linarith [P.depth]

/-- Numerators of the actual rate and group-density budgets. -/
def rateBase (k : ℕ) : ℝ := 3/(8*angularConstant k)
def etaBase (k : ℕ) : ℝ := rateBase k/4

theorem rateBase_pos (k : ℕ) : 0 < rateBase k := by unfold rateBase; positivity [angularConstant_pos k]
theorem etaBase_pos (k : ℕ) : 0 < etaBase k := div_pos (rateBase_pos k) (by norm_num)

theorem rate_budget {k M : ℕ} {F : TubeFamily (k+1) M} {δ beta : ℝ}
    (P : Pieces F δ beta) (hδ : 0 < δ) :
    rateBase k*(seedLog δ)^(-(1:ℝ)) ≤ retentionRate k P.J := by
  have hL := zero_lt_one.trans_le (seedLog_ge_one hδ (P.lower_scale.trans P.upper_scale))
  have hJ : 0 < (P.J:ℝ)+1 := by positivity
  have hD : 0 < 8*angularConstant k := by positivity [angularConstant_pos k]
  have hh := one_div_le_one_div_of_le hJ (depth_budget P hδ)
  have hm := mul_le_mul_of_nonneg_left hh (rateBase_pos k).le
  calc
    _ = rateBase k*(1/seedLog δ) := by rw [Real.rpow_neg_one]; ring
    _ ≤ rateBase k*(1/((P.J:ℝ)+1)) := hm
    _ = _ := by
      unfold rateBase retentionRate
      simp only [div_eq_mul_inv,mul_inv_rev]
      ring

theorem eta_budget {k M : ℕ} {F : TubeFamily (k+1) M} {δ beta : ℝ}
    (P : Pieces F δ beta) (hδ : 0 < δ) : etaBase k*(seedLog δ)^(-(1:ℝ)) ≤ P.eta := by
  have hh := div_le_div_of_nonneg_right (rate_budget P hδ) (by norm_num : (0:ℝ) ≤ 4)
  calc
    _ = (rateBase k*(seedLog δ)^(-(1:ℝ)))/4 := by unfold etaBase; ring
    _ ≤ retentionRate k P.J/4 := hh
    _ = _ := rfl

/-- The exact cap dependence of the positive logarithmic constant is A^-1/2. -/
theorem logarithmicConstant_cap_identity (k : ℕ) {angular eta alpha beta B K m A : ℝ}
    (hA : 0 ≤ A) :
    logarithmicConstant k angular eta alpha beta B K m A =
      logarithmicConstant k angular eta alpha beta B K m 1/Real.sqrt A := by
  have hcap : capCoefficient k angular m A = capCoefficient k angular m 1*A := by
    unfold capCoefficient
    ring
  unfold logarithmicConstant
  rw [hcap,Real.sqrt_mul' _ hA]
  ring

/-- The requested A^-1 cap loss follows uniformly for all A>=1. -/
theorem logarithmicConstant_cap_lower (k : ℕ) {angular eta alpha beta B K m A : ℝ}
    (hC : 0 ≤ logarithmicConstant k angular eta alpha beta B K m 1) (hA : 1 ≤ A) :
    logarithmicConstant k angular eta alpha beta B K m 1/A ≤
      logarithmicConstant k angular eta alpha beta B K m A := by
  rw [logarithmicConstant_cap_identity k (by linarith : 0 ≤ A)]
  exact div_le_div_of_nonneg_left hC (Real.sqrt_pos.mpr (by linarith))
    ((Real.sqrt_le_iff).mpr ⟨by linarith,by nlinarith⟩)

/-- Fixed physical two-ends constants inherit a prescribed logarithmic budget. -/
theorem ends_budget (k : ℕ) (width : ℝ) {B B₀ alpha L b : ℝ}
    (hB : B ≤ B₀*L^b) : endsConstant k width B alpha ≤ endsConstant k width B₀ alpha*L^b := by
  have hdim : 0 < 1+((k+1:ℕ):ℝ)/2 := by positivity
  have hh := mul_le_mul_of_nonneg_right
    (mul_le_mul_of_nonneg_right hB (Real.rpow_pos_of_pos hdim alpha).le)
    (Real.rpow_pos_of_pos (widthFactor_pos (k+1) width) alpha).le
  unfold endsConstant
  exact hh.trans_eq (by ring)

/-- Fixed positive constant for all scales, depths, densities and cap constants. -/
def uniformConstant (k : ℕ) (width alpha beta B₀ m : ℝ) : ℝ :=
  logarithmicConstant k 3 (etaBase (k+1)) alpha beta
    (endsConstant (k+1) width B₀ alpha) (broadConstant (k+1) beta) m 1*
    (3*rateBase (k+1)/16)/(widthFactor (k+2) width)^(k+2)

def uniformLoss (k : ℕ) (alpha beta b : ℝ) : ℝ := logarithmicLoss k alpha beta b 0 1+1

theorem uniformConstant_pos (k : ℕ) (width : ℝ) {alpha beta B₀ m : ℝ}
    (halpha : 0 < alpha) (hbeta : 0 < beta) (hB₀ : 1 ≤ B₀) (hm : 1 ≤ m) :
    0 < uniformConstant k width alpha beta B₀ m := by
  have hC := logarithmicConstant_pos k (alpha := alpha) (beta := beta) (by norm_num : (0:ℝ) ≤ 3) (etaBase_pos (k+1))
    (zero_lt_one.trans_le (endsConstant_ge_one (k+1) width hB₀ halpha.le))
    (zero_lt_one.trans_le (broadConstant_ge_one (k+1) hbeta.le))
    (zero_lt_one.trans_le (AngularBoxHairbrush.capCoefficient_ge_one k (by norm_num) (by linarith : 0 ≤ m) (by norm_num : (1:ℝ) ≤ 1)))
  unfold uniformConstant
  positivity [rateBase_pos (k+1),widthFactor_pos (k+2) width]

theorem uniformLoss_nonneg (k : ℕ) {alpha beta b : ℝ}
    (ha : 0 < alpha) (hb : 0 < beta) (hb₀ : 0 ≤ b) : 0 ≤ uniformLoss k alpha beta b := by
  have hh := logarithmicLoss_nonneg k ha hb hb₀ (by norm_num : (0:ℝ) ≤ 0) (by norm_num : (0:ℝ) ≤ 1)
  unfold uniformLoss
  linarith

/-- The complete finite-depth seed prefactor has a uniform logarithmic lower
bound, independent of actual depth, both scales, density, and cap constant. -/
theorem uniform_prefactor {k M : ℕ} {F : TubeFamily (k+2) M}
    {δ beta width alpha B B₀ b m A : ℝ} (P : Pieces F δ beta)
    (hδ : 0 < δ) (halpha : 0 < alpha) (hbeta : 0 < beta)
    (hB : 1 ≤ B) (hB₀ : 1 ≤ B₀) (hm : 1 ≤ m) (hA : 1 ≤ A)
    (hBB : B ≤ B₀*(seedLog δ)^b) :
    uniformConstant k width alpha beta B₀ m/A*(seedLog δ)^(-uniformLoss k alpha beta b) ≤
      (seedConstant k P.J width alpha beta B m A*(3*retentionRate (k+1) P.J/16)/
        (widthFactor (k+2) width)^(k+2))/(hairbrushLog k (δ/P.tau))^((5:ℝ)/2) := by
  have hδ1 := P.lower_scale.trans P.upper_scale
  have hL : 0 < seedLog δ := zero_lt_one.trans_le (seedLog_ge_one hδ hδ1)
  have htau : 0 < P.tau := hδ.trans_le P.lower_scale
  have hEnds := zero_lt_one.trans_le (endsConstant_ge_one (k+1) width hB halpha.le)
  have hEnds₀ := zero_lt_one.trans_le (endsConstant_ge_one (k+1) width hB₀ halpha.le)
  have hBroad := zero_lt_one.trans_le (broadConstant_ge_one (k+1) hbeta.le)
  have hCap := zero_lt_one.trans_le (AngularBoxHairbrush.capCoefficient_ge_one k
    (by norm_num : (0:ℝ) ≤ 3) (by linarith : 0 ≤ m) hA)
  have hCap₁ := zero_lt_one.trans_le (AngularBoxHairbrush.capCoefficient_ge_one k
    (by norm_num : (0:ℝ) ≤ 3) (by linarith : 0 ≤ m) (by norm_num : (1:ℝ) ≤ 1))
  have hC₁ := logarithmicConstant_pos k (alpha := alpha) (beta := beta)
    (by norm_num : (0:ℝ) ≤ 3) (etaBase_pos (k+1)) hEnds₀ hBroad hCap₁
  have hp := angular_prefactor_log_lower hδ P.lower_scale P.upper_scale
    (by norm_num : (0:ℝ) ≤ 3) P.eta_pos (etaBase_pos (k+1)) halpha hbeta hEnds hBroad hEnds₀ hBroad hCap hL
    (ends_budget (k+1) width hBB)
    (by simp : broadConstant (k+1) beta ≤ broadConstant (k+1) beta*(seedLog δ)^(0:ℝ))
    (eta_budget P hδ) (le_refl (hairbrushLog k δ))
  have hc := logarithmicConstant_cap_lower k hC₁.le hA
  have hp' := (mul_le_mul_of_nonneg_right hc
    (Real.rpow_pos_of_pos hL (-logarithmicLoss k alpha beta b 0 1)).le).trans hp
  have hr := rate_budget P hδ
  have hW : 0 < (widthFactor (k+2) width)^(k+2) := pow_pos (widthFactor_pos _ _) _
  have hf : (3*rateBase (k+1)/16)/(widthFactor (k+2) width)^(k+2)*(seedLog δ)^(-(1:ℝ)) ≤
      (3*retentionRate (k+1) P.J/16)/(widthFactor (k+2) width)^(k+2) := by
    have hh := mul_le_mul_of_nonneg_left hr
      (by positivity : (0:ℝ) ≤ (3/16)/(widthFactor (k+2) width)^(k+2))
    convert hh using 1 <;> first | rfl | ring
  have hlog := hairbrushLog_pos (k := k) (div_pos hδ htau) ((div_le_one htau).mpr P.lower_scale)
  have hseed := seedConstant_pos k P.J width (m := m) halpha hbeta hB hA
  have hmul := mul_le_mul hp' hf (by positivity [rateBase_pos (k+1)]) (by
    change 0 ≤ seedConstant k P.J width alpha beta B m A/(hairbrushLog k (δ/P.tau))^((5:ℝ)/2)
    positivity)
  calc
    _ = (logarithmicConstant k 3 (etaBase (k+1)) alpha beta (endsConstant (k+1) width B₀ alpha)
        (broadConstant (k+1) beta) m 1/A*(seedLog δ)^(-logarithmicLoss k alpha beta b 0 1))*
        ((3*rateBase (k+1)/16)/(widthFactor (k+2) width)^(k+2)*(seedLog δ)^(-(1:ℝ))) := by
      unfold uniformConstant uniformLoss
      rw [show -(logarithmicLoss k alpha beta b 0 1+1) = -logarithmicLoss k alpha beta b 0 1+ -(1:ℝ) by ring,
        Real.rpow_add hL]
      ring
    _ ≤ _ := hmul.trans_eq (by unfold seedConstant Pieces.eta; ring)

end
end KakeyaFormal.AngularSeedLogLoss
