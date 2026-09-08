import AngularSeedSummation
import AngularBoxAlgebra

/-! Direct application of the constructed single-box hairbrush theorem to
every actual retained angular group of an original finite shading. -/
namespace KakeyaFormal.AngularSeedHairbrush
open AngularSeedPieces AngularSeedRealization AngularSeedSummation AngularGroupRestriction
open AngularGroupPruning WidthNormalization MeasureTheory Set AngularBoxAlgebra HairbrushScales
open scoped BigOperators ENNReal
noncomputable section
open Classical

def broadConstant (k : ℕ) (beta : ℝ) : ℝ := (4:ℝ)^beta*(4*angularConstant k)

theorem broadConstant_ge_one (k : ℕ) {beta : ℝ} (hb : 0 ≤ beta) : 1 ≤ broadConstant k beta := by
  have hP := ProjectiveGeometry.packingConstant_ge_one k
  have hpow : (1:ℝ) ≤ (3:ℝ)^k := one_le_pow₀ (by norm_num)
  have hC : 1 ≤ angularConstant k := by unfold angularConstant; nlinarith
  have hfour : (1:ℝ) ≤ (4:ℝ)^beta := Real.one_le_rpow (by norm_num) hb
  unfold broadConstant
  nlinarith

theorem endsConstant_ge_one (k : ℕ) (width : ℝ) {B alpha : ℝ}
    (hB : 1 ≤ B) (ha : 0 ≤ alpha) : 1 ≤ endsConstant k width B alpha := by
  have hdim : (1:ℝ) ≤ 1+((k+1:ℕ):ℝ)/2 := by
    have hn : (0:ℝ) ≤ (k+1:ℕ) := Nat.cast_nonneg _
    linarith
  have h₁ := Real.one_le_rpow hdim ha
  have h₂ := Real.one_le_rpow (widthFactor_ge_one (k+1) width) ha
  exact one_le_mul_of_one_le_of_one_le (one_le_mul_of_one_le_of_one_le hB h₁) h₂

/-- Every actual retained group meets all premises of the full measurable
angular-box theorem, with no bounded-base or supplied-box premise. -/
theorem kept_group_hairbrush {k M : ℕ} (F : TubeFamily (k+2) M) {δ beta lam width alpha B m A : ℝ}
    (P : Pieces F δ beta) (hδ : 0 < δ) (hlam : 0 < lam) (hlam1 : lam ≤ 1)
    (halpha : 0 < alpha) (hbeta : 0 < beta) (hB : 1 ≤ B) (hm : 1 ≤ m) (hA : 1 ≤ A)
    (hadm : F.Admissible width δ) (hcomp : F.Comparable δ lam)
    (hsep : F.Separated δ) (hcap : F.CapBound δ m A)
    (hends : ∀ i, ∀ x : Space (k+2), ∀ r : ℝ, δ ≤ r → r ≤ 1 →
      (((F.shade i).filter (fun z => dist (cellCenter δ z) x ≤ r)).card:ℝ) ≤
        B*r^alpha*((F.shade i).card:ℝ))
    {g : Fin M} (hg : g ∈ P.keptGroups lam) :
    densityConstant k 3 P.eta alpha beta (endsConstant (k+1) width B alpha)
      (broadConstant (k+1) beta) m A*(physicalDensity (k+1) width lam)^2*
      ((active (P.shading g)).card:ℝ)*δ^(k+1)*(δ/P.tau)^((m-1)/2)/
      (hairbrushLog k (δ/P.tau))^((5:ℝ)/2) ≤
      (volume : Measure (Space (k+2))).real (groupUnion P width g) := by
  have hg₀ := kept_subset P.groups P.shading (P.eta*(lam/δ)) hg
  have hgpos := (kept_spec P.groups P.shading (P.eta*(lam/δ)) hg).1
  exact single_box_quadratic_density (AngularSeedRealization.family P width g)
    (Full P width g) (Ref P width g) (F.tube g).direction (0:Cell (k+1))
    hgpos (F.tube g).unit_direction hδ P.lower_scale P.upper_scale (by norm_num)
    P.eta_pos P.eta_le_one (physicalDensity_pos (k+1) width hlam) (physicalDensity_le_one _ _ hlam1)
    (endsConstant_ge_one (k+1) width hB halpha.le) halpha
    (broadConstant_ge_one (k+1) hbeta.le) hbeta hm hA
    (full_measurable P width g) (ref_measurable P width g) (ref_subset_full P width g)
    (full_carrier P hδ hadm g) (family_local P width hg₀)
    (AngularSeedRealization.family_separated P width g hsep)
    (AngularSeedRealization.family_cap_bound P width g hcap)
    (full_mass_upper P width hδ hcomp g) (kept_ref_mass_lower P width hδ hg)
    (ref_broad P width hδ hg₀) (fun i x r hr _ => full_two_ends P width hδ hB halpha.le hends g i x r hr)

/-- The actual positive single-group constant, before the explicit remaining
finite-depth/logarithmic loss is absorbed. -/
def seedConstant (k J : ℕ) (width alpha beta B m A : ℝ) : ℝ :=
  densityConstant k 3 (retentionRate (k+1) J/4) alpha beta
    (endsConstant (k+1) width B alpha) (broadConstant (k+1) beta) m A

theorem seedConstant_pos (k J : ℕ) (width : ℝ) {alpha beta B m A : ℝ}
    (halpha : 0 < alpha) (hbeta : 0 < beta) (hB : 1 ≤ B) (hA : 1 ≤ A) :
    0 < seedConstant k J width alpha beta B m A := by
  exact densityConstant_pos k (by norm_num) (div_pos (retentionRate_pos _ _) (by norm_num))
    (zero_lt_one.trans_le (endsConstant_ge_one _ _ hB halpha.le))
    (zero_lt_one.trans_le (broadConstant_ge_one _ hbeta.le)) (zero_lt_one.trans_le hA)

/-- Summing the concrete group hairbrush bounds uses the actual retained tube
count. The only losses displayed are depth, overlap, and the common map. -/
theorem summed_hairbrush {k M : ℕ} (F : TubeFamily (k+2) M) {δ beta lam width alpha B m A : ℝ}
    (P : Pieces F δ beta) (hδ : 0 < δ) (hlam : 0 < lam) (hlam1 : lam ≤ 1)
    (halpha : 0 < alpha) (hbeta : 0 < beta) (hB : 1 ≤ B) (hm : 1 ≤ m) (hA : 1 ≤ A)
    (hadm : F.Admissible width δ) (hcomp : F.Comparable δ lam)
    (hsep : F.Separated δ) (hcap : F.CapBound δ m A)
    (hends : ∀ i, ∀ x : Space (k+2), ∀ r : ℝ, δ ≤ r → r ≤ 1 →
      (((F.shade i).filter (fun z => dist (cellCenter δ z) x ≤ r)).card:ℝ) ≤
        B*r^alpha*((F.shade i).card:ℝ)) :
    seedConstant k P.J width alpha beta B m A*(physicalDensity (k+1) width lam)^2*
      ((3*retentionRate (k+1) P.J/8)*(M:ℝ))*δ^(k+1)*(δ/P.tau)^((m-1)/2)/
      (hairbrushLog k (δ/P.tau))^((5:ℝ)/2) ≤
      (2*P.tau^(-beta))*(δ^(k+2)*(F.unionCells.card:ℝ)/(widthFactor (k+2) width)^(k+2)) := by
  have htau : 0 < P.tau := hδ.trans_le P.lower_scale
  have hwidth : 0 < δ/P.tau := div_pos hδ htau
  have hwidth1 : δ/P.tau ≤ 1 := (div_le_one htau).mpr P.lower_scale
  have hC := seedConstant_pos k P.J width (m := m) halpha hbeta hB hA
  have hlog := hairbrushLog_pos (k := k) hwidth hwidth1
  have hcount := (P.pruning hδ hlam hcomp).2.2.2.1
  let factor : ℝ := seedConstant k P.J width alpha beta B m A*
    (physicalDensity (k+1) width lam)^2*δ^(k+1)*(δ/P.tau)^((m-1)/2)/
      (hairbrushLog k (δ/P.tau))^((5:ℝ)/2)
  have hfactor : 0 ≤ factor := by dsimp only [factor]; positivity
  have hpoint : ∀ g ∈ P.keptGroups lam,
      factor*((active (P.shading g)).card:ℝ) ≤
        (volume : Measure (Space (k+2))).real (groupUnion P width g) := by
    intro g hg
    have hh := kept_group_hairbrush F P hδ hlam hlam1 halpha hbeta hB hm hA hadm hcomp hsep hcap hends hg
    convert hh using 1; dsimp [factor,seedConstant,Pieces.eta]; ring
  calc
    _ = factor*((3*retentionRate (k+1) P.J/8)*(M:ℝ)) := by dsimp [factor]; ring
    _ ≤ factor*∑ g ∈ P.keptGroups lam, ((active (P.shading g)).card:ℝ) :=
      mul_le_mul_of_nonneg_left hcount hfactor
    _ = ∑ g ∈ P.keptGroups lam, factor*((active (P.shading g)).card:ℝ) := Finset.mul_sum _ _ _
    _ ≤ ∑ g ∈ P.keptGroups lam, (volume : Measure (Space (k+2))).real (groupUnion P width g) :=
      Finset.sum_le_sum hpoint
    _ ≤ _ := group_volume_sum P width lam hδ

end
end KakeyaFormal.AngularSeedHairbrush
