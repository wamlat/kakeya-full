import TwoEndsDiscreteEstimate
import TwoEndsGlobalizationAlgebra
import FiniteLocalizedFamily
import AngularRefinementBudgets
import CoarseBounds
import LocalizedTwoEndsApplication

/-! Actual removal of full two ends using the constructed common-radius and
common-density localized family. Geometric density control and retained
population are derived from the original cells; constants precede them. -/
namespace KakeyaFormal.TwoEndsGlobalization
open Finset FiniteGridLocalization FiniteLocalizedFamily AngularSeedLogLoss
open TwoEndsGlobalizationAlgebra
noncomputable section
open Classical

/-- At a sufficiently small original mesh, every whole shading is covered
by the unit ball about the actual midpoint of its unit tube. -/
theorem unit_ball_cover {n M : ℕ} (F : TubeFamily n M) {width δ : ℝ}
    (hadm : F.Admissible width δ) (hsmall : width*δ ≤ (1:ℝ)/2) :
    ∀ i z, z ∈ F.shade i → dist (cellCenter δ z) ((F.tube i).axisPoint (1/2)) ≤ 1 := by
  intro i z hz
  obtain ⟨t,ht,hdist⟩ := hadm i z hz
  have hmid : dist ((F.tube i).axisPoint t) ((F.tube i).axisPoint (1/2)) ≤ (1:ℝ)/2 := by
    rw [UnitTube.axisPoint_distance]
    apply abs_le.mpr
    exact ⟨by linarith [ht.1],by linarith [ht.2]⟩
  exact (dist_triangle _ _ _).trans ((add_le_add hdist hmid).trans (by linarith))

/-- Fixed coefficient in the actual common-radius/common-density population
budget, rewritten in the original natural logarithm. -/
def populationCoefficient (alpha : ℝ) : ℝ :=
  1/((alpha+3)*(AngularRefinementBudgets.logFactor)^2)

theorem populationCoefficient_pos {alpha : ℝ} (ha : 0 ≤ alpha) :
    0 < populationCoefficient alpha := by
  have hL := (AngularRefinementBudgets.constants_pos 0).1
  dsimp [populationCoefficient]
  positivity

/-- Both actual localization class depths cost at most two original logs;
this lower count is not a hypothesis of the globalization theorem. -/
theorem selected_population {n M : ℕ} {F : TubeFamily n M} {δ alpha lam : ℝ}
    (S : Selection F δ alpha lam) (hδ : 0 < δ) (ha : 0 ≤ alpha) :
    populationCoefficient alpha*(Real.log (2/δ))^(-(2:ℝ))*(M:ℝ) ≤ (S.selected.card:ℝ) := by
  have hδ1 := S.radius_lower.trans S.radius_upper
  have hseed : 0 < seedLog δ := zero_lt_one.trans_le (seedLog_ge_one hδ hδ1)
  have hL : 0 < Real.log (2/δ) := Real.log_pos ((lt_div_iff₀ hδ).mpr (by linarith))
  have hfactor := (AngularRefinementBudgets.constants_pos 0).1
  have hupper := AngularRefinementBudgets.seed_log_upper hδ hδ1
  have hden : (alpha+3)*(seedLog δ)^2 ≤
      (alpha+3)*(AngularRefinementBudgets.logFactor*Real.log (2/δ))^2 :=
    mul_le_mul_of_nonneg_left (pow_le_pow_left₀ hseed.le hupper 2) (by linarith)
  have hh := div_le_div_of_nonneg_left (Nat.cast_nonneg M) (by positivity) hden
  apply le_trans ?_ (selected_count_log S hδ ha)
  convert hh using 1
  rw [Real.rpow_neg hL.le,Real.rpow_two]
  unfold populationCoefficient
  field_simp


/-- Genuine geometric removal of full two ends. The local families, spatial
bins, normalized configurations, and all population/union comparisons are
constructed from the given shading. Only the density exponent changes. -/
theorem remove_two_ends {k : ℕ} {m D C : ℝ}
    (hestimate : TwoEndsDiscreteEstimate (k+1) m D C)
    (hm : 0 ≤ m) (hD : 1 ≤ D) (hC : 1 ≤ C) :
    DiscreteEstimate (k+1) m D (max D C) := by
  apply DiscreteEstimate.of_small_scales (hD.trans (le_max_left _ _))
  intro geom eps heps
  have heps2 : 0 < eps/2 := by positivity
  obtain ⟨alpha,eta,halpha,_halpha1,heta,hscalar⟩ :=
    uniform_globalization hD hC heps2
  have hB : (1:ℝ) ≤ (4:ℝ)^alpha := Real.one_le_rpow (by norm_num) halpha.le
  obtain ⟨cLocal,hcLocal,hlocal⟩ :=
    LocalizedTwoEndsApplication.localized_bound k (width := geom.width)
      hestimate halpha hB hm (zero_le_one.trans hC) heta
  let G := max 1 (LocalizedSeedNormalization.countConstant (k+1) geom.width)
  obtain ⟨cScale,hcScale,hscale⟩ := hscalar (G := G) (cNu := 1) (cLocal := cLocal)
    (a := 0) (le_max_left _ _) (by norm_num) hcLocal (by norm_num)
  obtain ⟨ell,hell,hlog⟩ := PivotLossAbsorption.inverse_log_delta
    (by norm_num : (0:ℝ) ≤ 2) heps2
  have hpop : 0 < populationCoefficient alpha := populationCoefficient_pos halpha.le
  refine ⟨1/(2*geom.width),cScale*populationCoefficient alpha*ell,
    by positivity [geom.width_pos],by positivity,?_⟩
  intro F hsmall
  have hδ := F.scale_pos
  have hAp : 0 < F.A := zero_lt_one.trans_le F.cap_ge_one
  by_cases hM : F.M = 0
  · simp only [hM,Nat.cast_zero,mul_zero]
    exact Nat.cast_nonneg _
  have hMp : 0 < F.M := Nat.pos_of_ne_zero hM
  have hwidth : geom.width*F.δ ≤ (1:ℝ)/2 := by
    have hh := mul_le_mul_of_nonneg_left hsmall geom.width_pos.le
    have hid : geom.width*(1/(2*geom.width)) = (1:ℝ)/2 := by field_simp [geom.width_pos.ne']
    exact hh.trans_eq hid
  obtain ⟨S⟩ := FiniteGridLocalization.exists_selection F.family hMp hδ F.scale_le_one
    halpha.le F.density_pos F.comparable (fun i => (F.family.tube i).axisPoint (1/2))
    (unit_ball_cover F.family F.admissible hwidth)
  have hselected : 0 < S.selected.card := Finset.card_pos.mpr S.nonempty
  have hrho : 0 < S.rho := hδ.trans_le S.radius_lower
  have hlocalS := hlocal S.selected.card (family S) F.δ S.rho S.s F.A
    hselected hδ S.radius_lower S.radius_upper S.density_pos F.cap_ge_one
    (family_admissible S F.admissible) (family_comparable S) (family_cap_bound S F.cap_bound)
    (fun i => S.centers (index S i)) (family_ball S) (family_two_ends S)
  have hsubset : ((family S).unionCells.card:ℝ) ≤ (F.family.unionCells.card:ℝ) :=
    Nat.cast_le.mpr (Finset.card_le_card (family_union_subset S))
  have hupper : S.s ≤ G*S.rho := (selected_density_upper S hδ F.admissible).trans
    (mul_le_mul_of_nonneg_right (le_max_right _ _) hrho.le)
  have hlower : (1:ℝ)*(Real.log (2/F.δ))^(-(0:ℝ))*S.rho^alpha*F.lam ≤ S.s := by
    simpa only [neg_zero,Real.rpow_zero,one_mul] using S.density_lower
  have hscaleS : cScale*F.A⁻¹*F.δ^(m-D+eps/2)*F.lam^(max D C)*(S.selected.card:ℝ) ≤
      (F.family.unionCells.card:ℝ) :=
    hscale hδ S.radius_lower S.radius_upper S.density_pos F.density_pos
      (Nat.cast_nonneg _) hAp hupper hlower (hlocalS.trans hsubset)
  have hpopulation := selected_population S hδ halpha.le
  have hlogs := hlog F.δ hδ F.scale_le_one
  have hδpow : F.δ^(m-D+eps) = F.δ^(m-D+eps/2)*F.δ^(eps/2) := by
    rw [← Real.rpow_add hδ]
    congr 1
    ring
  calc
    _ = (cScale*F.A⁻¹*F.δ^(m-D+eps/2)*F.lam^(max D C))*
        (populationCoefficient alpha*(ell*F.δ^(eps/2))*(F.M:ℝ)) := by
      rw [hδpow]
      ring
    _ ≤ (cScale*F.A⁻¹*F.δ^(m-D+eps/2)*F.lam^(max D C))*
        (populationCoefficient alpha*(Real.log (2/F.δ))^(-(2:ℝ))*(F.M:ℝ)) := by
      gcongr
      positivity [F.density_pos]
    _ ≤ (cScale*F.A⁻¹*F.δ^(m-D+eps/2)*F.lam^(max D C))*(S.selected.card:ℝ) :=
      mul_le_mul_of_nonneg_left hpopulation (by positivity [F.density_pos])
    _ ≤ _ := hscaleS

end
end KakeyaFormal.TwoEndsGlobalization
