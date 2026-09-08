import AngularSeedEstimate

/-! Preserve the exact square-root cap dependence of the constructed finite
all-angle two-ends hairbrush seed. These theorems concern actual finite grid
shadings; no arbitrary-measurable angular decomposition is asserted here. -/
namespace KakeyaFormal.AngularSeedSqrtCap
open AngularSeedPieces AngularSeedRealization AngularSeedBound AngularSeedHairbrush AngularSeedLogLoss
open AngularBoxAlgebra AngularBoxLogLoss AngularBoxRecovery HairbrushScales WidthNormalization
open AngularSeedEstimate
noncomputable section

/-- The original prefactor retains its exact A^(-1/2) dependence. -/
theorem uniform_prefactor {k M : ℕ} {F : TubeFamily (k+2) M}
    {δ beta width alpha B B₀ b m A : ℝ} (P : Pieces F δ beta)
    (hδ : 0 < δ) (halpha : 0 < alpha) (hbeta : 0 < beta)
    (hB : 1 ≤ B) (hB₀ : 1 ≤ B₀) (hm : 1 ≤ m) (hA : 1 ≤ A)
    (hBB : B ≤ B₀*(seedLog δ)^b) :
    uniformConstant k width alpha beta B₀ m/Real.sqrt A*(seedLog δ)^(-uniformLoss k alpha beta b) ≤
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
  have hp := angular_prefactor_log_lower hδ P.lower_scale P.upper_scale
    (by norm_num : (0:ℝ) ≤ 3) P.eta_pos (etaBase_pos (k+1)) halpha hbeta hEnds hBroad hEnds₀ hBroad hCap hL
    (ends_budget (k+1) width hBB)
    (by simp : broadConstant (k+1) beta ≤ broadConstant (k+1) beta*(seedLog δ)^(0:ℝ))
    (eta_budget P hδ) (le_refl (hairbrushLog k δ))
  have hp' := hp
  rw [logarithmicConstant_cap_identity k (by linarith : 0 ≤ A)] at hp'
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
        (broadConstant (k+1) beta) m 1/Real.sqrt A*(seedLog δ)^(-logarithmicLoss k alpha beta b 0 1))*
        ((3*rateBase (k+1)/16)/(widthFactor (k+2) width)^(k+2)*(seedLog δ)^(-(1:ℝ))) := by
      unfold uniformConstant uniformLoss
      rw [show -(logarithmicLoss k alpha beta b 0 1+1) = -logarithmicLoss k alpha beta b 0 1+ -(1:ℝ) by ring,
        Real.rpow_add hL]
      ring
    _ ≤ _ := hmul.trans_eq (by unfold seedConstant Pieces.eta; ring)


/-- Actual finite-grid estimate with all logarithmic losses exposed. -/
theorem logarithmic_seed_with_pieces {k M : ℕ} (F : TubeFamily (k+2) M)
    {δ beta lam width alpha B B₀ b m A : ℝ} (P : Pieces F δ beta)
    (hδ : 0 < δ) (hlam : 0 < lam) (hlam1 : lam ≤ 1)
    (halpha : 0 < alpha) (hbeta : 0 < beta) (hbetaS : beta ≤ (m-1)/2)
    (hB : 1 ≤ B) (hB₀ : 1 ≤ B₀) (hm : 1 ≤ m) (hA : 1 ≤ A)
    (hBB : B ≤ B₀*(seedLog δ)^b)
    (hadm : F.Admissible width δ) (hcomp : F.Comparable δ lam)
    (hsep : F.Separated δ) (hcap : F.CapBound δ m A)
    (hends : ∀ i, ∀ x : Space (k+2), ∀ r : ℝ, δ ≤ r → r ≤ 1 →
      (((F.shade i).filter (fun z => dist (cellCenter δ z) x ≤ r)).card:ℝ) ≤
        B*r^alpha*((F.shade i).card:ℝ)) :
    uniformConstant k width alpha beta B₀ m/Real.sqrt A*(seedLog δ)^(-uniformLoss k alpha beta b)*
      lam^2*(M:ℝ)*δ^((m-3)/2) ≤ (F.unionCells.card:ℝ) := by
  have hbase := finite_seed_at_depth F P hδ hlam hlam1 halpha hbeta hbetaS hB hm hA hadm hcomp hsep hcap hends
  have hpre := uniform_prefactor (width := width) P hδ halpha hbeta hB hB₀ hm hA hBB
  have hfac : 0 ≤ lam^2*(M:ℝ)*δ^(k+1)*δ^((m-1)/2) := by positivity
  have hvolume := (mul_le_mul_of_nonneg_right hpre hfac).trans (by
    convert hbase using 1 <;> first | rfl | ring)
  have hpow : δ^(k+2)*δ^((m-3)/2) = δ^(k+1)*δ^((m-1)/2) := by
    rw [← Real.rpow_natCast,← Real.rpow_natCast,← Real.rpow_add hδ,← Real.rpow_add hδ]
    congr 1
    push_cast
    ring
  apply (mul_le_mul_iff_right₀ (pow_pos hδ (k+2))).mp
  calc
    _ = (uniformConstant k width alpha beta B₀ m/Real.sqrt A*(seedLog δ)^(-uniformLoss k alpha beta b))*
        (lam^2*(M:ℝ)*(δ^(k+2)*δ^((m-3)/2))) := by ring
    _ = _ := by rw [hpow]; ring
    _ ≤ _ := hvolume


/-- The finite-grid theorem after uniform epsilon absorption. -/
theorem two_ends_seed (k : ℕ) {width alpha beta B₀ b m eps : ℝ}
    (halpha : 0 < alpha) (hbeta : 0 < beta) (hbetaS : beta ≤ (m-1)/2)
    (hB₀ : 1 ≤ B₀) (hb : 0 ≤ b) (hm : 1 ≤ m) (heps : 0 < eps) :
    ∃ c : ℝ, 0 < c ∧ ∀ M : ℕ, ∀ F : TubeFamily (k+2) M, ∀ δ lam B A : ℝ,
      0 < δ → δ ≤ 1 → 0 < lam → lam ≤ 1 → 1 ≤ B → 1 ≤ A →
      B ≤ B₀*(seedLog δ)^b → F.Admissible width δ → F.Comparable δ lam →
      F.Separated δ → F.CapBound δ m A →
      (∀ i, ∀ x : Space (k+2), ∀ r : ℝ, δ ≤ r → r ≤ 1 →
        (((F.shade i).filter (fun z => dist (cellCenter δ z) x ≤ r)).card:ℝ) ≤
          B*r^alpha*((F.shade i).card:ℝ)) →
      c*(Real.sqrt A)⁻¹*lam^2*(M:ℝ)*δ^((m-3)/2+eps) ≤ (F.unionCells.card:ℝ) := by
  obtain ⟨ell,hell,hlog⟩ := seedLog_absorption (uniformLoss_nonneg k halpha hbeta hb) heps
  have hC := uniformConstant_pos k width halpha hbeta hB₀ hm
  refine ⟨uniformConstant k width alpha beta B₀ m*ell,mul_pos hC hell,?_⟩
  intro M F δ lam B A hδ hδ1 hlam hlam1 hB hA hBB hadm hcomp hsep hcap hends
  by_cases hM : 0 < M
  · obtain ⟨P⟩ := exists_pieces F hM hδ hδ1 hbeta.le
    have hh := logarithmic_seed_with_pieces F P hδ hlam hlam1 halpha hbeta hbetaS
      hB hB₀ hm hA hBB hadm hcomp hsep hcap hends
    have hfac : 0 ≤ uniformConstant k width alpha beta B₀ m/Real.sqrt A*lam^2*(M:ℝ)*δ^((m-3)/2) := by positivity
    have hmult := mul_le_mul_of_nonneg_left (hlog δ hδ hδ1) hfac
    calc
      _ = (uniformConstant k width alpha beta B₀ m/Real.sqrt A*lam^2*(M:ℝ)*δ^((m-3)/2))*(ell*δ^eps) := by
        rw [Real.rpow_add hδ]
        simp only [div_eq_mul_inv]
        ring
      _ ≤ _ := hmult
      _ = uniformConstant k width alpha beta B₀ m/Real.sqrt A*(seedLog δ)^(-uniformLoss k alpha beta b)*
          lam^2*(M:ℝ)*δ^((m-3)/2) := by ring
      _ ≤ _ := hh
  · have hz : M = 0 := by omega
    simp only [hz,Nat.cast_zero,mul_zero,zero_mul]
    exact Nat.cast_nonneg _


/-- All angular pieces are constructed, and the positive broadness exponent is
chosen from the fixed parameter m>1. No epsilon weakening is needed. -/
theorem logarithmic_seed (k : ℕ) {width alpha B₀ b m : ℝ}
    (halpha : 0 < alpha) (hB₀ : 1 ≤ B₀) (hb : 0 ≤ b) (hm : 1 < m) :
    ∃ c P : ℝ, 0 < c ∧ 0 ≤ P ∧
      ∀ M : ℕ, ∀ F : TubeFamily (k+2) M, ∀ δ lam B A : ℝ,
      0 < δ → δ ≤ 1 → 0 < lam → lam ≤ 1 → 1 ≤ B → 1 ≤ A →
      B ≤ B₀*(seedLog δ)^b → F.Admissible width δ → F.Comparable δ lam →
      F.Separated δ → F.CapBound δ m A →
      (∀ i, ∀ x : Space (k+2), ∀ r : ℝ, δ ≤ r → r ≤ 1 →
        (((F.shade i).filter (fun z => dist (cellCenter δ z) x ≤ r)).card:ℝ) ≤
          B*r^alpha*((F.shade i).card:ℝ)) →
      c*(Real.sqrt A)⁻¹*(seedLog δ)^(-P)*lam^2*(M:ℝ)*δ^((m-3)/2) ≤
        (F.unionCells.card:ℝ) := by
  let beta : ℝ := min (1/2) ((m-1)/4)
  have hbeta : 0 < beta := lt_min (by norm_num) (by linarith)
  have hbetaS : beta ≤ (m-1)/2 := by
    have h := min_le_right (1/2:ℝ) ((m-1)/4)
    dsimp only [beta]
    linarith
  refine ⟨uniformConstant k width alpha beta B₀ m,uniformLoss k alpha beta b,
    uniformConstant_pos k width halpha hbeta hB₀ hm.le,
    uniformLoss_nonneg k halpha hbeta hb,?_⟩
  intro M F δ lam B A hδ hδ1 hlam hlam1 hB hA hBB hadm hcomp hsep hcap hends
  by_cases hM : 0 < M
  · obtain ⟨P⟩ := exists_pieces F hM hδ hδ1 hbeta.le
    simpa only [div_eq_mul_inv] using logarithmic_seed_with_pieces F P hδ hlam hlam1
      halpha hbeta hbetaS hB hB₀ hm.le hA hBB hadm hcomp hsep hcap hends
  · have hz : M = 0 := by omega
    simp only [hz,Nat.cast_zero,mul_zero,zero_mul]
    exact Nat.cast_nonneg _

theorem natural_log_le_seedLog {δ : ℝ} (hδ : 0 < δ) (hδ1 : δ ≤ 1) :
    Real.log (2/δ) ≤ seedLog δ := by
  have hlog2 : 0 < Real.log (2:ℝ) := Real.log_pos (by norm_num)
  have hlog2one : Real.log (2:ℝ) ≤ 1 := by
    have h := Real.log_le_sub_one_of_pos (by norm_num : (0:ℝ)<2)
    linarith
  have hlog : 0 ≤ Real.log (2/δ) := Real.log_nonneg ((le_div_iff₀ hδ).mpr (by linarith))
  have hdiv : Real.log (2/δ) ≤ Real.log (2/δ)/Real.log 2 :=
    (le_div_iff₀ hlog2).mpr (by nlinarith)
  unfold seedLog Real.logb
  linarith

/-- Literal natural-log loss and square-root cap dependence, for actual
finite-grid shadings at every positive scale at most one. -/
theorem natural_logarithmic_seed (k : ℕ) {width alpha B₀ b m : ℝ}
    (halpha : 0 < alpha) (hB₀ : 1 ≤ B₀) (hb : 0 ≤ b) (hm : 1 < m) :
    ∃ c P : ℝ, 0 < c ∧ 0 ≤ P ∧
      ∀ M : ℕ, ∀ F : TubeFamily (k+2) M, ∀ δ lam B A : ℝ,
      0 < δ → δ ≤ 1 → 0 < lam → lam ≤ 1 → 1 ≤ B → 1 ≤ A →
      B ≤ B₀*(Real.log (2/δ))^b → F.Admissible width δ → F.Comparable δ lam →
      F.Separated δ → F.CapBound δ m A →
      (∀ i, ∀ x : Space (k+2), ∀ r : ℝ, δ ≤ r → r ≤ 1 →
        (((F.shade i).filter (fun z => dist (cellCenter δ z) x ≤ r)).card:ℝ) ≤
          B*r^alpha*((F.shade i).card:ℝ)) →
      c*(Real.sqrt A)⁻¹*(Real.log (2/δ))^(-P)*lam^2*(M:ℝ)*δ^((m-3)/2) ≤
        (F.unionCells.card:ℝ) := by
  obtain ⟨c,P,hc,hP,hmain⟩ := logarithmic_seed k (width:=width) halpha hB₀ hb hm
  have hC : 0 < (3:ℝ)/Real.log 2 := div_pos (by norm_num) (Real.log_pos (by norm_num))
  refine ⟨c*((3:ℝ)/Real.log 2)^(-P),P,mul_pos hc (Real.rpow_pos_of_pos hC _),hP,?_⟩
  intro M F δ lam B A hδ hδ1 hlam hlam1 hB hA hBB hadm hcomp hsep hcap hends
  have hL : 0 < Real.log (2/δ) := Real.log_pos ((lt_div_iff₀ hδ).mpr (by linarith))
  have hLS : 0 < seedLog δ := zero_lt_one.trans_le (seedLog_ge_one hδ hδ1)
  have hBseed : B ≤ B₀*(seedLog δ)^b := hBB.trans
    (mul_le_mul_of_nonneg_left (Real.rpow_le_rpow hL.le (natural_log_le_seedLog hδ hδ1) hb) (by linarith))
  have hs := Real.rpow_le_rpow_of_nonpos hLS (seedLog_upper hδ hδ1) (neg_nonpos.mpr hP)
  rw [Real.mul_rpow hC.le hL.le] at hs
  have hfac : 0 ≤ c*(Real.sqrt A)⁻¹*lam^2*(M:ℝ)*δ^((m-3)/2) := by positivity
  have h := mul_le_mul_of_nonneg_left hs hfac
  calc
    _ = (c*(Real.sqrt A)⁻¹*lam^2*(M:ℝ)*δ^((m-3)/2))*
        (((3:ℝ)/Real.log 2)^(-P)*(Real.log (2/δ))^(-P)) := by ring
    _ ≤ _ := h
    _ = c*(Real.sqrt A)⁻¹*(seedLog δ)^(-P)*lam^2*(M:ℝ)*δ^((m-3)/2) := by ring
    _ ≤ _ := hmain M F δ lam B A hδ hδ1 hlam hlam1 hB hA hBseed hadm hcomp hsep hcap hends

end
end KakeyaFormal.AngularSeedSqrtCap
