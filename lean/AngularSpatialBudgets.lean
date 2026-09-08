import AngularRefinementBudgets
import AngularSpatialSampling

/-! Fixed conditioning and population budgets for all actual good spatial
boxes of an angular reference refinement. The same boxes and full sets are
used by the separately constructed sampling outputs. -/
namespace KakeyaFormal.AngularSpatialBudgets
open Finset AngularSeedPieces AngularRestrictedRefinement AngularRefinementBudgets
open AngularSpatialSampling AnisotropicSamplingBudgets
open scoped BigOperators
noncomputable section

def effectiveCoefficient (k : ℕ) : ℝ :=
  AnisotropicSamplingInput.retention k 3 (1/(16*depthFactor k))

def endsCoefficient (k : ℕ) (width B alpha : ℝ) : ℝ :=
  (4*B/etaCoefficient k)*(1+((k+1:ℕ):ℝ)/2)^alpha*
    (WidthNormalization.widthFactor (k+1) width)^alpha

def broadCoefficient (k : ℕ) (beta : ℝ) : ℝ :=
  AngularRestrictedRefinement.broadCoefficient k beta*64*depthFactor k*spatialConstant k/etaCoefficient k

def boxPopulationCoefficient (k : ℕ) : ℝ := etaCoefficient k/(512*(depthFactor k)^2)

theorem coefficients_pos (k : ℕ) (width beta alpha : ℝ) {B : ℝ} (hB : 0 < B) :
    0 < effectiveCoefficient k ∧ 0 < endsCoefficient k width B alpha ∧
      0 < broadCoefficient k beta ∧ 0 < boxPopulationCoefficient k := by
  obtain ⟨_,he,hd⟩ := constants_pos k
  have heff : 0 < effectiveCoefficient k := AnisotropicSamplingInput.retention_pos _ _ (by positivity)
  have hw := WidthNormalization.widthFactor_pos (k+1) width
  have hb := AngularRestrictedRefinement.broadCoefficient_pos k beta
  have hs := spatialConstant_pos k
  refine ⟨heff,?_,?_,?_⟩ <;> dsimp [endsCoefficient,broadCoefficient,boxPopulationCoefficient] <;> positivity

variable {k M : ℕ} {F : TubeFamily (k+1) M} {δ beta lam B alpha : ℝ}
variable {P : Pieces F δ beta} {g : Fin M}

theorem effective_budget (V : Refinement P lam B alpha g)
    (hδ : 0 < δ) (hL : 1 ≤ Real.log (2/δ)) :
    effectiveCoefficient k*(Real.log (2/δ))^(-(1:ℝ)) ≤ effectiveRatio V := by
  have hh := div_le_div_of_nonneg_right (marked_ratio_budget V hδ hL) (by norm_num : (0:ℝ)≤4)
  have hratio : (1/(16*depthFactor k))*(Real.log (2/δ))^(-(1:ℝ)) ≤ markedRatio V/4 := by
    simp only [markedRatio,div_eq_mul_inv,mul_inv_rev] at hh ⊢
    convert hh using 1 <;> first | rfl | ring
  exact retention_budget k 3 hratio

theorem ends_budget (V : Refinement P lam B alpha g) (width : ℝ)
    (hδ : 0 < δ) (hL : 1 ≤ Real.log (2/δ)) (hB : 0 ≤ B) :
    AngularSpatialSampling.endsConstant V width ≤
      endsCoefficient k width B alpha*(Real.log (2/δ))^((1:ℝ)) := by
  have hh := inverse_retention (constants_pos k).2.1 (zero_lt_one.trans_le hL)
    P.eta_pos (eta_budget P hδ)
  have hw := WidthNormalization.widthFactor_pos (k+1) width
  have hf : 0 ≤ 4*B*(1+((k+1:ℕ):ℝ)/2)^alpha*
      (WidthNormalization.widthFactor (k+1) width)^alpha := by positivity
  have ht := mul_le_mul_of_nonneg_left hh hf
  simp only [AngularSpatialSampling.endsConstant,endsCoefficient,div_eq_mul_inv] at ht ⊢
  convert ht using 1 <;> first | rfl | ring

theorem broad_budget (V : Refinement P lam B alpha g)
    (hδ : 0 < δ) (hL : 1 ≤ Real.log (2/δ)) :
    AngularSpatialSampling.broadConstant V*(4*spatialConstant k) ≤
      broadCoefficient k beta*(Real.log (2/δ))^((2:ℝ)) := by
  have hLp : 0 < Real.log (2/δ) := zero_lt_one.trans_le hL
  have hh := inverse_retention (constants_pos k).2.1 hLp P.eta_pos (eta_budget P hδ)
  have hd : ((V.depth+1:ℕ):ℝ) ≤ depthFactor k*Real.log (2/δ) := by simpa using depth_budget V hδ hL
  have hf : 0 ≤ AngularRestrictedRefinement.broadCoefficient k beta*64*spatialConstant k := by
    positivity [AngularRestrictedRefinement.broadCoefficient_pos k beta,spatialConstant_pos k]
  have hprod := mul_le_mul hd hh (inv_nonneg.mpr P.eta_pos.le)
    (mul_nonneg (constants_pos k).2.2.le hLp.le)
  have ht := mul_le_mul_of_nonneg_left hprod hf
  simp only [AngularSpatialSampling.broadConstant,broadCoefficient,Real.rpow_one,Real.rpow_two,
    div_eq_mul_inv] at ht ⊢
  convert ht using 1 <;> first | rfl | ring

/-- Summed population of ALL actual good boxes of this refined angular group.
The loss is three powers of the original logarithm, independently of group. -/
theorem box_population (V : Refinement P lam B alpha g) {width R : ℝ}
    (T : SpatialData V width R) (hδ : 0 < δ) (hlam : 0 < lam)
    (hL : 1 ≤ Real.log (2/δ)) :
    boxPopulationCoefficient k*(Real.log (2/δ))^(-(3:ℝ))*
      ((AngularGroupRestriction.active (P.shading g)).card:ℝ) ≤
        ∑ q ∈ boxes V width, ((SpatialMarkedPartition.indices
          (SpatialGridPopulation.refinedLabel V width) q).card:ℝ) := by
  have hp := population_budget V hδ hlam hL
  have hr := marked_ratio_budget V hδ hL
  have he := (constants_pos k).2.1
  have hd := (constants_pos k).2.2
  have hmul := mul_le_mul hr hp (by positivity : 0 ≤
      (etaCoefficient k/(32*depthFactor k))*(Real.log (2/δ))^(-(2:ℝ))*
        ((AngularGroupRestriction.active (P.shading g)).card:ℝ)) (markedRatio_pos V).le
  have hh := div_le_div_of_nonneg_right hmul (by norm_num : (0:ℝ)≤4)
  apply le_trans ?_ T.population
  have hLp : 0 < Real.log (2/δ) := zero_lt_one.trans_le hL
  have hid : (Real.log (2/δ))^(-(1:ℝ))*(Real.log (2/δ))^(-(2:ℝ)) =
      (Real.log (2/δ))^(-(3:ℝ)) := by rw [← Real.rpow_add hLp]; norm_num
  convert hh using 1
  · dsimp [boxPopulationCoefficient]
    have hdep := (constants_pos k).2.2.ne'
    field_simp
    rw [← hid]
    ring
  · rfl

/-- The complete population of all actual retained angular/spatial boxes
 has a uniform inverse-fourth-logarithm lower bound. -/
theorem total_population (P : Pieces F δ beta) {width R : ℝ}
    (hδ : 0 < δ) (hlam : 0 < lam) (hcomp : F.Comparable δ lam)
    (hL : 1 ≤ Real.log (2/δ))
    (V : ∀ g : ↥(P.keptGroups lam), Refinement P lam B alpha g.val)
    (T : ∀ g : ↥(P.keptGroups lam), SpatialData (V g) width R) :
    (boxPopulationCoefficient k*(3*etaCoefficient k/2))*(Real.log (2/δ))^(-(4:ℝ))*(M:ℝ) ≤
      ∑ g : ↥(P.keptGroups lam), ∑ q ∈ boxes (V g) width,
        ((SpatialMarkedPartition.indices (SpatialGridPopulation.refinedLabel (V g) width) q).card:ℝ) := by
  let L := Real.log (2/δ)
  have hLp : 0 < L := zero_lt_one.trans_le hL
  have he := (constants_pos k).2.1
  have hd := (constants_pos k).2.2
  have hc : 0 < boxPopulationCoefficient k := by dsimp [boxPopulationCoefficient]; positivity
  have hkeep := (P.pruning hδ hlam hcomp).2.2.2.1
  have heta := mul_le_mul_of_nonneg_right (eta_budget P hδ) (Nat.cast_nonneg M)
  have hfirst : (3*etaCoefficient k/2)*L^(-(1:ℝ))*(M:ℝ) ≤
      ∑ g : ↥(P.keptGroups lam), ((AngularGroupRestriction.active (P.shading g.val)).card:ℝ) := by
    have hh := mul_le_mul_of_nonneg_left heta (by norm_num : (0:ℝ)≤3/2)
    have hstep : (3*etaCoefficient k/2)*L^(-(1:ℝ))*(M:ℝ) ≤
        (3*retentionRate k P.J/8)*(M:ℝ) := by
      dsimp only [L,Pieces.eta] at hh ⊢
      convert hh using 1 <;> first | rfl | ring
    have hsum : (∑ g ∈ P.keptGroups lam, ((AngularGroupRestriction.active (P.shading g)).card:ℝ)) =
        ∑ g : ↥(P.keptGroups lam), ((AngularGroupRestriction.active (P.shading g.val)).card:ℝ) :=
      sum_subtype _ (fun _ => Iff.rfl) _
    exact (hstep.trans hkeep).trans_eq hsum
  have hsecond : boxPopulationCoefficient k*L^(-(3:ℝ))*
      (∑ g : ↥(P.keptGroups lam), ((AngularGroupRestriction.active (P.shading g.val)).card:ℝ)) ≤
      ∑ g : ↥(P.keptGroups lam), ∑ q ∈ boxes (V g) width,
        ((SpatialMarkedPartition.indices (SpatialGridPopulation.refinedLabel (V g) width) q).card:ℝ) := by
    rw [mul_sum]
    exact sum_le_sum (fun g _ => box_population (V g) (T g) hδ hlam hL)
  have hh := mul_le_mul_of_nonneg_left hfirst (by positivity : 0 ≤ boxPopulationCoefficient k*L^(-(3:ℝ)))
  apply le_trans ?_ hsecond
  convert hh using 1
  rw [show (-(4:ℝ)) = -3 + -1 by norm_num,Real.rpow_add hLp]
  ring

end
end KakeyaFormal.AngularSpatialBudgets
