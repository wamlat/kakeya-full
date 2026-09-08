import AngularSpatialBudgets
import AngularSeedSummation
import PivotLossAbsorption

/-! Summation of estimates for the actual original-cell spatial boxes.
Density and population losses follow from the constructed refinements; the
only analytic interface is a uniform estimate for each of those same boxes. -/
namespace KakeyaFormal.AngularSpatialSummation
open Finset AngularSeedPieces AngularRestrictedRefinement AngularSpatialSampling
open AngularRefinementBudgets AngularSpatialBudgets
open scoped BigOperators
noncomputable section

/-- The original angular overlap is cancelled by the positive angular gain,
and the actual density/population logarithms cost only an arbitrary scale loss. -/
theorem cancel_logarithmic_overlap {c cD cP K beta s C loss : ℝ}
    (hc : 0 < c) (hcD : 0 < cD) (hcP : 0 < cP) (hK : 0 < K)
    (hC : 0 ≤ C) (hbeta : beta ≤ s) (hloss : 0 < loss) :
    ∃ c₀ : ℝ, 0 < c₀ ∧ ∀ {δ tau lam A M E : ℝ},
      0 < δ → δ ≤ 1 → 0 < tau → tau ≤ 1 → 0 < lam → 1 ≤ A → 0 ≤ M →
      c*A⁻¹*(δ/tau)^s*(cD*(Real.log (2/δ))^(-(1:ℝ))*lam)^C*
        (cP*(Real.log (2/δ))^(-(4:ℝ))*M) ≤ K*tau^(-beta)*E →
      c₀*A⁻¹*δ^(s+loss)*lam^C*M ≤ E := by
  obtain ⟨ell,hell,hlogs⟩ := PivotLossAbsorption.inverse_log_delta
    (by linarith : 0 ≤ C+4) hloss
  refine ⟨c*cD^C*cP*ell/K,by positivity,?_⟩
  intro δ tau lam A M E hδ hδ1 htau htau1 hlam hA hM hbound
  let L := Real.log (2/δ)
  have hL : 0 < L := Real.log_pos ((lt_div_iff₀ hδ).mpr (by linarith))
  have hpow : (cD*L^(-(1:ℝ))*lam)^C*(cP*L^(-(4:ℝ))*M) =
      cD^C*cP*L^(-(C+4))*lam^C*M := by
    rw [Real.mul_rpow (by positivity : 0 ≤ cD*L^(-(1:ℝ))) hlam.le,
      Real.mul_rpow hcD.le (Real.rpow_nonneg hL.le _),← Real.rpow_mul hL.le]
    calc
      _ = cD^C*cP*(L^((-1)*C)*L^(-(4:ℝ)))*lam^C*M := by ring
      _ = _ := by rw [← Real.rpow_add hL,show (-1)*C + -4 = -(C+4) by ring]
  have hl := hlogs δ hδ hδ1
  have hgain := AngularSeedSummation.angular_gain_absorbs_overlap hδ htau htau1 hbeta
  let f := (c*cD^C*cP/K)*A⁻¹*lam^C*M
  have hf : 0 ≤ f := by dsimp [f]; positivity
  calc
    _ = f*δ^s*(ell*δ^loss) := by rw [Real.rpow_add hδ]; dsimp [f]; ring
    _ ≤ f*δ^s*L^(-(C+4)) := mul_le_mul_of_nonneg_left hl (by positivity)
    _ ≤ f*(tau^beta*(δ/tau)^s)*L^(-(C+4)) :=
      mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hgain hf) (Real.rpow_nonneg hL.le _)
    _ = (tau^beta/K)*(c*A⁻¹*(δ/tau)^s*((cD*L^(-(1:ℝ))*lam)^C*(cP*L^(-(4:ℝ))*M))) := by
      rw [hpow]
      dsimp [f]
      ring
    _ ≤ (tau^beta/K)*(K*tau^(-beta)*E) := by
      apply mul_le_mul_of_nonneg_left _ (by positivity)
      simpa only [mul_assoc] using hbound
    _ = E := by
      rw [Real.rpow_neg htau.le]
      have ht := (Real.rpow_pos_of_pos htau beta).ne'
      field_simp

/-- All original-grid estimates are summed over the SAME actual boxes.
No density lower bound, population lower bound or overlap bound is assumed:
those are obtained from the proved refinement and spatial constructions. -/
theorem from_piece_estimates (k : ℕ) (width beta C s loss cPiece : ℝ)
    (hC : 0 ≤ C) (hbeta : beta ≤ s) (hloss : 0 < loss) (hcPiece : 0 < cPiece) :
    ∃ c : ℝ, 0 < c ∧ ∀ {M : ℕ} (F : TubeFamily (k+1) M) {δ lam B alpha R A : ℝ}
      (P : Pieces F δ beta),
      0 < δ → 0 < lam → 1 ≤ A → F.Comparable δ lam → F.Admissible width δ →
      1 ≤ Real.log (2/δ) →
      ∀ (V : ∀ g : ↥(P.keptGroups lam), Refinement P lam B alpha g.val)
        (_T : ∀ g : ↥(P.keptGroups lam), SpatialData (V g) width R),
      (∀ g : ↥(P.keptGroups lam), ∀ q ∈ boxes (V g) width,
        cPiece*A⁻¹*(δ/P.tau)^s*(physicalDensity (V g) width)^C*
          ((SpatialMarkedPartition.indices (SpatialGridPopulation.refinedLabel (V g) width) q).card:ℝ) ≤
            ((SpatialGridPopulation.refinedCells (V g) width q).card:ℝ)) →
      c*A⁻¹*δ^(s+loss)*lam^C*(M:ℝ) ≤ (F.unionCells.card:ℝ) := by
  let W := WidthNormalization.widthFactor (k+1) width
  let cD := etaCoefficient k/(2*W^(k+1))
  let cP := boxPopulationCoefficient k*(3*etaCoefficient k/2)
  have hw : 0 < W := WidthNormalization.widthFactor_pos _ _
  obtain ⟨_,he,hd⟩ := constants_pos k
  have hcp0 : 0 < boxPopulationCoefficient k := by dsimp [boxPopulationCoefficient]; positivity
  have hcD : 0 < cD := by dsimp [cD]; positivity
  have hcP : 0 < cP := by dsimp [cP]; positivity
  have hsp := spatialConstant_pos k
  obtain ⟨c,hc,hmain⟩ := cancel_logarithmic_overlap hcPiece hcD hcP
    (by positivity : 0 < 2*spatialConstant k) hC hbeta hloss
  refine ⟨c,hc,?_⟩
  intro M F δ lam B alpha R A P hδ hlam hA hcomp hadm hL V T hpieces
  let L := Real.log (2/δ)
  have hLp : 0 < L := zero_lt_one.trans_le hL
  let low := cD*L^(-(1:ℝ))*lam
  have hlow : 0 ≤ low := by dsimp [low]; positivity
  have hdensity (g : ↥(P.keptGroups lam)) : low ≤ physicalDensity (V g) width :=
    density_budget (V g) W hδ hw hlam.le
  have hcount := AngularSpatialSampling.total_old_count P hδ hadm V
  have hpop := AngularSpatialBudgets.total_population P hδ hlam hcomp hL V T
  have hcommon : 0 ≤ cPiece*A⁻¹*(δ/P.tau)^s := by
    have htau : 0 < P.tau := hδ.trans_le P.lower_scale
    positivity
  have hsummed : cPiece*A⁻¹*(δ/P.tau)^s*low^C*
      (∑ g : ↥(P.keptGroups lam), ∑ q ∈ boxes (V g) width,
        ((SpatialMarkedPartition.indices (SpatialGridPopulation.refinedLabel (V g) width) q).card:ℝ)) ≤
      ∑ g : ↥(P.keptGroups lam), ∑ q ∈ boxes (V g) width,
        ((SpatialGridPopulation.refinedCells (V g) width q).card:ℝ) := by
    simp_rw [mul_sum]
    apply sum_le_sum
    intro g _
    apply sum_le_sum
    intro q hq
    have hh := Real.rpow_le_rpow hlow (hdensity g) hC
    have ht := mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hh hcommon)
      (Nat.cast_nonneg (SpatialMarkedPartition.indices (SpatialGridPopulation.refinedLabel (V g) width) q).card)
    exact ht.trans (hpieces g q hq)
  apply hmain hδ (P.lower_scale.trans P.upper_scale) (hδ.trans_le P.lower_scale)
    P.upper_scale hlam hA (Nat.cast_nonneg M)
  have hh := mul_le_mul_of_nonneg_left hpop (mul_nonneg hcommon (Real.rpow_nonneg hlow C))
  have ht := (hh.trans hsummed).trans hcount
  simpa only [cP,low,mul_assoc,mul_comm,mul_left_comm] using ht

end
end KakeyaFormal.AngularSpatialSummation
