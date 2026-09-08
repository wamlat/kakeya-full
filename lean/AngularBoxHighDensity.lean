import AngularSpatialBudgets
import AnisotropicHighDensity

/-! Apply the high-density sampling estimate to the SAME actual output of
each good spatial box. Original-log conditioning budgets and old-cell support
are derived from the actual angular refinement, not supplied per box. -/
namespace KakeyaFormal.AngularBoxHighDensity
open Finset AngularSeedPieces AngularRestrictedRefinement AngularSpatialSampling
open WidthNormalization SpatialMarkedPartition
noncomputable section

/-- Constants precede the original family, both scales, the angular pieces,
refinement, all actual good boxes, and their simultaneously constructed output.
The only remaining branch tests are the displayed coarse complement and high
output density, together with a fixed normalized small-scale cutoff. -/
theorem construct {k : ℕ} {m d d' pExp qExp : ℝ}
    (hbase : DiscreteEstimate (k+2) m d pExp)
    (hlift : DiscreteEstimate (k+3) d d' qExp)
    (hm : 0 ≤ m) (hp : 1 ≤ pExp) (hd : 0 ≤ d) (hqExp : 2 ≤ qExp)
    (hD : KakeyaScalar.pivotSet m d' < m+1)
    (width R B alpha beta eps a : ℝ)
    (hB : 1 ≤ B) (ha : 0 < alpha) (hbeta : 0 < beta)
    (heps : 0 < eps) (haScale : 1 ≤ a) :
    ∃ δ₀ : ℝ, 0 < δ₀ ∧ δ₀ ≤ 1 ∧ ∃ c : ℝ, 0 < c ∧
      ∀ {M : ℕ} {F : TubeFamily (k+2) M} {δ lam A : ℝ}
      (P : Pieces F δ beta) (g : Fin M) (V : Refinement P lam B alpha g)
      (U : Package V width R m A) (q : ↥(boxes V width)),
      0 < δ → 1 ≤ A → δ/P.tau ≤ δ₀ → (δ/P.tau)^a ≤ δ →
      (1/(δ/P.tau))^(-(1:ℝ)/3) ≤ (U.output q).density →
      c*A⁻¹*(δ/P.tau)^(m-KakeyaScalar.pivotSet m d'+eps)*
        (physicalDensity V width)^(KakeyaScalar.pivotDensity pExp qExp)*
        ((indices (SpatialGridPopulation.refinedLabel V width) q.val).card:ℝ) ≤
          ((SpatialGridPopulation.refinedCells V width q.val).card:ℝ) := by
  obtain ⟨he₀,hB₀,hK₀,_hpop⟩ := AngularSpatialBudgets.coefficients_pos (k+1) width beta alpha
    (zero_lt_one.trans_le hB)
  obtain ⟨δs,hδs,hδs1,cS,hcS,hmain⟩ := AnisotropicHighDensity.original_log_parameters hbase hlift hm hp hd hqExp hD
    1 (AnisotropicJointGeometry.baseBound 3 (R+2) (((k+1:ℕ):ℝ)+4)) 3
    (AngularSpatialBudgets.effectiveCoefficient (k+1))
    (AngularSpatialBudgets.endsCoefficient (k+1) width B alpha)
    (AngularSpatialBudgets.broadCoefficient (k+1) beta) alpha beta 1 1 2 eps a
    (by norm_num) (by norm_num) he₀ hB₀ hK₀ ha hbeta haScale
    (by norm_num) (by norm_num) (by norm_num) heps
  let capC := AnisotropicJointGeometry.capFactor (k+1) 3 m
  have hcapC : 1 ≤ capC := AnisotropicJointGeometry.capFactor_ge_one (k+1) (by norm_num) hm
  have hcapCp : 0 < capC := zero_lt_one.trans_le hcapC
  refine ⟨min δs (2/Real.exp 1),lt_min hδs (by positivity),
    (min_le_left _ _).trans hδs1,cS/capC,div_pos hcS hcapCp,?_⟩
  intro M F δ lam A P g V U q hδ hA hscale hcompare hhigh
  have htau : 0 < P.tau := hδ.trans_le P.lower_scale
  have hold_new : δ ≤ δ/P.tau := (le_div_iff₀ htau).mpr (by
    simpa only [mul_one] using mul_le_mul_of_nonneg_left P.upper_scale hδ.le)
  have hold_cutoff : δ ≤ 2/Real.exp 1 := hold_new.trans (hscale.trans (min_le_right _ _))
  have hL : 1 ≤ Real.log (2/δ) := by
    apply (Real.le_log_iff_exp_le (div_pos (by norm_num) hδ)).mpr
    apply (le_div_iff₀ hδ).mpr
    simpa only [mul_comm] using (le_div_iff₀ (Real.exp_pos 1)).mp hold_cutoff
  have hAout : 1 ≤ capC*A := hcapC.trans (le_mul_of_one_le_right hcapCp.le hA)
  have hh := hmain (boxFull V width q.val) (F.tube g).direction q.val
    (SpatialGridPopulation.refinedCells V width q.val) (U.output q)
    hδ htau P.upper_scale (widthFactor_ge_one (k+2) width) hAout
    (box_full_support V width q.val) (hscale.trans (min_le_left _ _)) hcompare hhigh
    (AngularSpatialBudgets.effective_budget V hδ hL)
    (AngularSpatialBudgets.ends_budget V width hδ hL (zero_le_one.trans hB))
    (AngularSpatialBudgets.broad_budget V hδ hL)
  simpa only [capC,mul_inv_rev,div_eq_mul_inv,mul_assoc,mul_comm,mul_left_comm] using hh

end
end KakeyaFormal.AngularBoxHighDensity
