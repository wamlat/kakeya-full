import AngularRestrictedRefinement
import AngularSeedLogLoss
import AnisotropicSamplingBudgets

/-! Uniform natural-logarithm budgets of the actual angular reference
refinement. The finite depth and population losses are derived from the
constructed pieces and marked mass, rather than assumed class-count bounds. -/
namespace KakeyaFormal.AngularRefinementBudgets
open AngularSeedPieces AngularRestrictedRefinement AnisotropicSamplingBudgets
noncomputable section

def logFactor : ℝ := 3/Real.log 2
def etaCoefficient (k : ℕ) : ℝ := AngularSeedLogLoss.etaBase k/logFactor
def depthFactor (k : ℕ) : ℝ := depthCoefficient (etaCoefficient k) 1

theorem constants_pos (k : ℕ) : 0 < logFactor ∧ 0 < etaCoefficient k ∧ 0 < depthFactor k := by
  have hl : 0 < logFactor := div_pos (by norm_num) (Real.log_pos (by norm_num))
  exact ⟨hl,div_pos (AngularSeedLogLoss.etaBase_pos k) hl,
    depthCoefficient_pos (by norm_num)⟩

theorem seed_log_upper {δ : ℝ} (hδ : 0 < δ) (hδ1 : δ ≤ 1) :
    AngularSeedLogLoss.seedLog δ ≤ logFactor*Real.log (2/δ) := by
  have hlog2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hL : Real.log 2 ≤ Real.log (2/δ) := Real.log_le_log (by norm_num)
    ((le_div_iff₀ hδ).mpr (by linarith))
  dsimp [AngularSeedLogLoss.seedLog,Real.logb,logFactor]
  calc
    _ ≤ Real.log (2/δ)/Real.log 2+2*Real.log (2/δ)/Real.log 2 := by
      exact add_le_add (le_refl _) ((le_div_iff₀ hlog2).mpr (by linarith))
    _ = _ := by ring

theorem eta_budget {k M : ℕ} {F : TubeFamily (k+1) M} {δ beta : ℝ}
    (P : Pieces F δ beta) (hδ : 0 < δ) :
    etaCoefficient k*(Real.log (2/δ))^(-(1:ℝ)) ≤ P.eta := by
  have hδ1 := P.lower_scale.trans P.upper_scale
  have hs : 0 < AngularSeedLogLoss.seedLog δ :=
    zero_lt_one.trans_le (AngularSeedLogLoss.seedLog_ge_one hδ hδ1)
  have hh := one_div_le_one_div_of_le hs (seed_log_upper hδ hδ1)
  have hm := mul_le_mul_of_nonneg_left hh (AngularSeedLogLoss.etaBase_pos k).le
  apply le_trans ?_ (AngularSeedLogLoss.eta_budget P hδ)
  simpa only [etaCoefficient,Real.rpow_neg_one,div_eq_mul_inv,mul_inv_rev,one_mul,mul_assoc,mul_comm,mul_left_comm] using hm

theorem depth_budget {k M : ℕ} {F : TubeFamily (k+1) M} {δ beta lam B alpha : ℝ}
    {P : Pieces F δ beta} {g : Fin M} (V : Refinement P lam B alpha g)
    (hδ : 0 < δ) (hL : 1 ≤ Real.log (2/δ)) :
    (V.depth:ℝ)+1 ≤ depthFactor k*Real.log (2/δ) :=
  AnisotropicSamplingBudgets.depth_bound (constants_pos k).2.1 (by norm_num)
    hL P.eta_pos (eta_budget P hδ) V.depth_bound

theorem marked_ratio_budget {k M : ℕ} {F : TubeFamily (k+1) M} {δ beta lam B alpha : ℝ}
    {P : Pieces F δ beta} {g : Fin M} (V : Refinement P lam B alpha g)
    (hδ : 0 < δ) (hL : 1 ≤ Real.log (2/δ)) :
    (1/(4*depthFactor k))*(Real.log (2/δ))^(-(1:ℝ)) ≤ 1/(4*(V.depth+1:ℕ)) := by
  have hh : ((V.depth+1:ℕ):ℝ) ≤ depthFactor k*Real.log (2/δ) := by simpa using depth_budget V hδ hL
  have ht := one_div_le_one_div_of_le (by positivity : (0:ℝ)<4*(V.depth+1:ℕ))
    (mul_le_mul_of_nonneg_left hh (by norm_num : (0:ℝ)≤4))
  simpa only [Real.rpow_neg_one,div_eq_mul_inv,mul_inv_rev,mul_assoc,mul_comm,mul_left_comm] using ht

theorem population_budget {k M : ℕ} {F : TubeFamily (k+1) M} {δ beta lam B alpha : ℝ}
    {P : Pieces F δ beta} {g : Fin M} (V : Refinement P lam B alpha g)
    (hδ : 0 < δ) (hlam : 0 < lam) (hL : 1 ≤ Real.log (2/δ)) :
    (etaCoefficient k/(32*depthFactor k))*(Real.log (2/δ))^(-(2:ℝ))*
      ((AngularGroupRestriction.active (P.shading g)).card:ℝ) ≤ (V.N:ℝ) := by
  have hh := per_depth_retention (constants_pos k).2.1 (by norm_num : (0:ℝ)≤1)
    (zero_lt_one.trans_le hL) (eta_budget P hδ) (depth_budget V hδ hL)
  have ht := div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_right hh
    (Nat.cast_nonneg (AngularGroupRestriction.active (P.shading g)).card)) (by norm_num : (0:ℝ)≤32)
  apply le_trans ?_ (V.population_lower hδ hlam)
  norm_num only [show (1:ℝ)+1=2 by norm_num] at ht
  convert ht using 1 <;> simp only [depthFactor,div_eq_mul_inv,mul_inv_rev] <;> ring

theorem density_budget {k M : ℕ} {F : TubeFamily (k+1) M} {δ beta lam B alpha : ℝ}
    {P : Pieces F δ beta} {g : Fin M} (V : Refinement P lam B alpha g) (W : ℝ)
    (hδ : 0 < δ) (hW : 0 < W) (hlam : 0 ≤ lam) :
    (etaCoefficient k/(2*W^(k+1)))*(Real.log (2/δ))^(-(1:ℝ))*lam ≤
      V.density/W^(k+1) := by
  have hh := div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_right (eta_budget P hδ) hlam)
    (by norm_num : (0:ℝ)≤2)
  have ht := div_le_div_of_nonneg_right (hh.trans V.density_lower) (pow_pos hW (k+1)).le
  calc
    _ = etaCoefficient k*(Real.log (2/δ))^(-(1:ℝ))*lam/2/W^(k+1) := by
      simp only [div_eq_mul_inv,mul_inv_rev]
      ring
    _ ≤ _ := ht

end
end KakeyaFormal.AngularRefinementBudgets
