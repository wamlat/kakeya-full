import HairbrushKernel

/-!
# Explicit logarithmic dependence of the actual hairbrush kernel

All constants are fixed before the physical scale and density. The exponents
alpha and beta may be arbitrarily small positive reals; the logarithmic loss is
allowed to depend on them, while the scale and density exponents are unchanged.
-/
namespace KakeyaFormal.HairbrushLogLoss
open KakeyaFormal.HairbrushScales KakeyaFormal.HairbrushKernel
open KakeyaFormal.HairbrushSelection KakeyaFormal.HairbrushAllScales
open MeasureTheory
noncomputable section

/-- A logarithmic upper bound on a concentration constant gives an explicit
lower bound on its density-independent chosen radius. -/
theorem radius_log_lower {B B₀ alpha L b : ℝ}
    (hB : 0 < B) (hB₀ : 0 < B₀) (ha : 0 < alpha) (hL : 0 < L)
    (hbound : B ≤ B₀*L^b) :
    concentrationRadius B₀ alpha*L^(-b/alpha) ≤ concentrationRadius B alpha := by
  have h := Real.rpow_le_rpow_of_nonpos (by positivity : 0 < 2*B)
    (mul_le_mul_of_nonneg_left hbound (by norm_num : (0:ℝ) ≤ 2))
    (by exact div_nonpos_of_nonpos_of_nonneg (by norm_num) ha.le : -1/alpha ≤ 0)
  have hid : (2*(B₀*L^b))^(-1/alpha) = concentrationRadius B₀ alpha*L^(-b/alpha) := by
    rw [show 2*(B₀*L^b) = (2*B₀)*L^b by ring,
      Real.mul_rpow (by positivity : 0 ≤ 2*B₀) (by positivity : 0 ≤ L^b),
      ← Real.rpow_mul hL.le]
    unfold concentrationRadius
    congr 2
    ring
  rw [hid] at h
  exact h

def lossPower (k : ℕ) (alpha beta b q : ℝ) : ℝ :=
  (k+1:ℕ)*(b/alpha+q/beta)+5/2

theorem lossPower_nonneg (k : ℕ) {alpha beta b q : ℝ}
    (ha : 0 < alpha) (hb : 0 < beta) (hb₀ : 0 ≤ b) (hq : 0 ≤ q) :
    0 ≤ lossPower k alpha beta b q := by
  unfold lossPower
  positivity

def radiusConstant (k : ℕ) (B₀ K₀ alpha beta : ℝ) : ℝ :=
  (concentrationRadius B₀ alpha*concentrationRadius K₀ beta)^(k+1)/
    (logCoefficient k)^((5:ℝ)/2)

theorem radiusConstant_pos (k : ℕ) {B₀ K₀ alpha beta : ℝ}
    (hB₀ : 0 < B₀) (hK₀ : 0 < K₀) : 0 < radiusConstant k B₀ K₀ alpha beta := by
  have hB := concentrationRadius_pos (alpha := alpha) hB₀
  have hK := concentrationRadius_pos (alpha := beta) hK₀
  have hC := logCoefficient_ge_one k
  unfold radiusConstant
  positivity

/-- Exact scalar logarithmic loss from both chosen radii and the real
inverse-angle/multiplicity logarithm. No density parameter occurs in P. -/
theorem hairbrush_prefactor_log_lower {k : ℕ} {δ B K B₀ K₀ alpha beta L b q : ℝ}
    (hδ : 0 < δ) (hδ1 : δ ≤ 1)
    (hB : 0 < B) (hK : 0 < K) (hB₀ : 0 < B₀) (hK₀ : 0 < K₀)
    (ha : 0 < alpha) (hb : 0 < beta) (hL : 0 < L)
    (hBB : B ≤ B₀*L^b) (hKK : K ≤ K₀*L^q)
    (hlog : hairbrushLog k δ ≤ logCoefficient k*L) :
    radiusConstant k B₀ K₀ alpha beta*L^(-lossPower k alpha beta b q) ≤
      (concentrationRadius B alpha*concentrationRadius K beta)^(k+1)/
        (hairbrushLog k δ)^((5:ℝ)/2) := by
  have h₁ := radius_log_lower hB hB₀ ha hL hBB
  have h₂ := radius_log_lower hK hK₀ hb hL hKK
  have hB₀r := concentrationRadius_pos (alpha := alpha) hB₀
  have hKr := concentrationRadius_pos (alpha := beta) hK
  have hBr := concentrationRadius_pos (alpha := alpha) hB
  have hK₀r := concentrationRadius_pos (alpha := beta) hK₀
  have hmul := mul_le_mul h₁ h₂ (by positivity) hBr.le
  have hid₁ : (concentrationRadius B₀ alpha*L^(-b/alpha)) *
      (concentrationRadius K₀ beta*L^(-q/beta)) =
      (concentrationRadius B₀ alpha*concentrationRadius K₀ beta)*L^(-(b/alpha+q/beta)) := by
    calc
      _ = (concentrationRadius B₀ alpha*concentrationRadius K₀ beta)*(L^(-b/alpha)*L^(-q/beta)) := by ring
      _ = _ := by rw [← Real.rpow_add hL]; congr 2; ring
  rw [hid₁] at hmul
  have hpow := pow_le_pow_left₀ (by positivity : 0 ≤
    (concentrationRadius B₀ alpha*concentrationRadius K₀ beta)*L^(-(b/alpha+q/beta))) hmul (k+1)
  have hid₂ : ((concentrationRadius B₀ alpha*concentrationRadius K₀ beta)*L^(-(b/alpha+q/beta)))^(k+1) =
      (concentrationRadius B₀ alpha*concentrationRadius K₀ beta)^(k+1)*
        L^(-((k+1:ℕ)*(b/alpha+q/beta))) := by
    rw [mul_pow,← Real.rpow_mul_natCast hL.le]
    congr 2
    ring
  rw [hid₂] at hpow
  have hlogpos := hairbrushLog_pos (k := k) hδ hδ1
  have hC := logCoefficient_ge_one k
  have hden := Real.rpow_le_rpow hlogpos.le hlog (by norm_num : (0:ℝ) ≤ 5/2)
  have hdiv := div_le_div₀ (by positivity : 0 ≤
    (concentrationRadius B alpha*concentrationRadius K beta)^(k+1)) hpow
    (by positivity : 0 < (hairbrushLog k δ)^((5:ℝ)/2)) hden
  have hid₃ : ((concentrationRadius B₀ alpha*concentrationRadius K₀ beta)^(k+1)*
      L^(-((k+1:ℕ)*(b/alpha+q/beta)))) / (logCoefficient k*L)^((5:ℝ)/2) =
      radiusConstant k B₀ K₀ alpha beta*L^(-lossPower k alpha beta b q) := by
    rw [Real.mul_rpow (by linarith : 0 ≤ logCoefficient k) hL.le]
    calc
      _ = ((concentrationRadius B₀ alpha*concentrationRadius K₀ beta)^(k+1)/(logCoefficient k)^((5:ℝ)/2))*
          (L^(-((k+1:ℕ)*(b/alpha+q/beta)))/L^((5:ℝ)/2)) := by ring
      _ = _ := by
        rw [← Real.rpow_sub hL]
        unfold radiusConstant lossPower
        congr 2
        ring
  rwa [hid₃] at hdiv

/-- Enlargement of the physical width decreases the needed logarithm. This
permits the original scale logarithm to budget every angularly rescaled piece. -/
theorem hairbrushLog_mono_width {k : ℕ} {δ₀ δ : ℝ}
    (hδ₀ : 0 < δ₀) (hδ : δ₀ ≤ δ) : hairbrushLog k δ ≤ hairbrushLog k δ₀ := by
  have hd : 0 < δ := hδ₀.trans_le hδ
  have hr := div_le_div_of_nonneg_left (by norm_num : (0:ℝ) ≤ 2) hδ₀ hδ
  have hl := Real.logb_le_logb_of_le (by norm_num : (1:ℝ) < 2) (by positivity : 0 < 2/δ) hr
  have hC := logCoefficient_ge_one k
  exact mul_le_mul_of_nonneg_left (by linarith : Real.logb 2 (2/δ)+2 ≤ Real.logb 2 (2/δ₀)+2) (by linarith)

/-- The original actual geometric data yield an explicit polynomial logarithmic
loss with fixed constants. The real-m physical exponent and density exponents
are exactly preserved; the loss power has no density dependence. -/
theorem logarithmic_hairbrush_kernel {k M : ℕ} (F : TubeFamily (k+2) M)
    (Y : Fin M → Set (Space (k+2))) (G : Set (Space (k+2)))
    {δ lam B alpha beta K m A upper B₀ K₀ L b q : ℝ} (hM : 0 < M)
    (hδ : 0 < δ) (hδ1 : δ ≤ 1) (hB : 1 ≤ B) (ha : 0 < alpha) (hK : 1 ≤ K) (hb : 0 < beta) (hlam : 0 ≤ lam) (hlam1 : lam ≤ 1) (hlamu : lam ≤ upper)
    (hm : 1 ≤ m) (hA : 1 ≤ A) (hu : 0 < upper) (hsep : F.Separated δ)
    (hY : ∀ i, MeasurableSet (Y i)) (hsub : ∀ i, Y i ⊆ (F.tube i).carrier δ)
    (hG : MeasurableSet G)
    (hgood : (∑ i, (volume : Measure (Space (k+2))).real (Y i))/2 ≤ markedMass (ν := volume) Y G)
    (hbroad : PointwiseBroad F Y G δ beta K)
    (hmass : ∀ i, lam*δ^(k+1) ≤ (volume : Measure (Space (k+2))).real (Y i))
    (hends : ∀ i p t, δ ≤ t → t ≤ 1 →
      (volume : Measure (Space (k+2))).real (Y i ∩ Metric.closedBall p t) ≤
        B*t^alpha*(volume : Measure (Space (k+2))).real (Y i))
    (hcap : F.CapBound δ m A)
    (hupper : ∀ i, (volume : Measure (Space (k+2))).real (Y i) ≤ upper*δ^(k+1))
    (hB₀ : 0 < B₀) (hK₀ : 0 < K₀) (hL : 0 < L)
    (hBB : B ≤ B₀*L^b) (hKK : K ≤ K₀*L^q)
    (hlog : hairbrushLog k δ ≤ logCoefficient k*L) :
    radiusConstant k B₀ K₀ alpha beta*L^(-lossPower k alpha beta b q)*markedMass (ν := volume) Y G*
        lam^((3:ℝ)/2)*δ^((m-1)/2)/(allScaleConstant k*Real.sqrt (A*upper)) ≤
      (volume : Measure (Space (k+2))).real (⋃ i, Y i) := by
  have hcore := chosen_radius_hairbrush F Y G hM hδ hδ1 hB ha hK hb
    hlam hlam1 hlamu hm hA hu hsep hY hsub hG hgood hbroad hmass hends hcap hupper
  have hpre := hairbrush_prefactor_log_lower hδ hδ1 (by linarith : 0 < B) (by linarith : 0 < K)
    hB₀ hK₀ ha hb hL hBB hKK hlog
  have hW : 0 ≤ markedMass (ν := volume) Y G := Finset.sum_nonneg (fun _ _ => measureReal_nonneg)
  have hC := allScaleConstant_pos k
  have hApos : 0 < A := by linarith
  have hfactor : 0 ≤ markedMass (ν := volume) Y G*lam^((3:ℝ)/2)*δ^((m-1)/2)/
      (allScaleConstant k*Real.sqrt (A*upper)) := by positivity
  have hh := mul_le_mul_of_nonneg_right hpre hfactor
  have hid₁ : (radiusConstant k B₀ K₀ alpha beta*L^(-lossPower k alpha beta b q))*
      (markedMass (ν := volume) Y G*lam^((3:ℝ)/2)*δ^((m-1)/2)/(allScaleConstant k*Real.sqrt (A*upper))) =
      radiusConstant k B₀ K₀ alpha beta*L^(-lossPower k alpha beta b q)*markedMass (ν := volume) Y G*
        lam^((3:ℝ)/2)*δ^((m-1)/2)/(allScaleConstant k*Real.sqrt (A*upper)) := by ring
  have hid₂ : ((concentrationRadius B alpha*concentrationRadius K beta)^(k+1)/(hairbrushLog k δ)^((5:ℝ)/2))*
      (markedMass (ν := volume) Y G*lam^((3:ℝ)/2)*δ^((m-1)/2)/(allScaleConstant k*Real.sqrt (A*upper))) =
      (concentrationRadius B alpha*concentrationRadius K beta)^(k+1)*markedMass (ν := volume) Y G*
        lam^((3:ℝ)/2)*δ^((m-1)/2)/(allScaleConstant k*Real.sqrt (A*upper)*(hairbrushLog k δ)^((5:ℝ)/2)) := by ring
  rw [hid₁,hid₂] at hh
  exact hh.trans hcore

end
end KakeyaFormal.HairbrushLogLoss

#print axioms KakeyaFormal.HairbrushLogLoss.hairbrush_prefactor_log_lower

#print axioms KakeyaFormal.HairbrushLogLoss.logarithmic_hairbrush_kernel
