import OriginalPivotSlabs
import ConstructedPivotClosing

/-! The original marked-input package supplies every geometric datum used by
actual lifted grouped pruning and closing energy. Fixed graph/spatial factors
are absorbed before the original cutoff or configuration is chosen. -/
namespace KakeyaFormal.OriginalPivotEnergy
open Finset ActualLabelSelection AngleFiberSelection
open OriginalPivotSlabs SelectedBaseFamilies SelectedColoredFamilies
open scoped BigOperators
noncomputable section
open Classical

/-- Fixed factor converting the original pruning cutoff to the actual lifted
cap coefficient. There is no kappa or scale dependence in this factor. -/
def geometricFactor (k : ℕ) (width baseRadius d : ℝ) : ℝ :=
  PrunedGraphLift.spatialConstant (k+2) width baseRadius d*
    (16+2*(2*width+((k+2:ℕ):ℝ)/2))^d

theorem geometricFactor_pos (k : ℕ) {width baseRadius d : ℝ}
    (hw : 0 ≤ width) (hd : 0 ≤ d) : 0 < geometricFactor k width baseRadius d := by
  have hsp := spatial_coefficient_ge_one (k+2) (width:=width) (baseRadius:=baseRadius)
    hd (le_refl (1:ℝ))
  simp only [mul_one] at hsp
  have hpos : 0 < PrunedGraphLift.spatialConstant (k+2) width baseRadius d :=
    zero_lt_one.trans_le hsp
  dsimp [geometricFactor]
  positivity

/-- Exact factorization, keeping the actual cutoff separate from the fixed
spatial and graph-chart constants. -/
theorem cap_factorization (k : ℕ) (width baseRadius d L : ℝ) :
    capCoefficient (k:=k+1) (width:=width) d
      (PrunedGraphLift.spatialConstant (k+2) width baseRadius d*L) =
        geometricFactor k width baseRadius d*L := by
  unfold capCoefficient geometricFactor
  ring

/-- Actual original-input closing energy, with no new geometric, incidence,
retention, cap, sample or energy hypothesis beyond the constructed package.
The positive coefficient is chosen before K and every original configuration. -/
theorem construct {k : ℕ} {d d' r eps : ℝ}
    (width baseRadius : ℝ) (hw : 0 ≤ width) (hd : 0 ≤ d)
    (hlift : DiscreteEstimate (k+3) d d' r) (hr : 1 ≤ r) (heps : 0 < eps) :
    ∃ c : ℝ, 0 < c ∧ ∀ (K : ℝ) {M : ℕ}
      (F : TubeFamily (k+2) M) (E : Finset (Cell (k+2)))
      (marks : Fin M → Finset (Cell (k+2)))
      {δ A lam xi B theta m p alpha : ℝ}
      (U : Package F E marks K δ A lam xi B theta width baseRadius m d p eps alpha),
      ∃ rho : ℝ, 0 < rho ∧
        SelectedOutputDensity.lowerCoefficient (k+1) width*(kappa width B theta alpha)^6*
          (((2^U.selection.level:ℕ):ℝ)*δ) ≤ rho ∧
        c*(kappa width B theta alpha)^5*(cutoff K E δ A lam xi m d p eps M U.depth)⁻¹*
          rho^r*δ^(d-d'+1+eps)*(outputSupport U.selection.retained).card ≤ (E.card : ℝ)^2 := by
  obtain ⟨c₀,hc₀,hclose⟩ := ConstructedPivotClosing.construct
    (k:=k+1) (R:=baseRadius) hw hd hlift hr heps
  let c := c₀/geometricFactor k width baseRadius d
  have hc : 0 < c := div_pos hc₀ (geometricFactor_pos k hw hd)
  refine ⟨c,hc,?_⟩
  intro K M F E marks δ A lam xi B theta m p alpha U
  let L := cutoff K E δ A lam xi m d p eps M U.depth
  let Cball := PrunedGraphLift.spatialConstant (k+2) width baseRadius d*L
  obtain ⟨families,hrho,hlower,henergy⟩ := hclose
    U.kappa_pos U.recovered.admissible U.selection U.lines Cball U.scale_pos
    U.geometry.original_scale_le_one U.kappa_le_one U.normalized_coefficient_ge_one
    U.recovered.bounded U.normalized_spatial U.geometry.attached_witness_small
  let rho := SelectedOutputDensity.rho U.selection U.lines (color U.selection)
    (shading U.selection U.lines families)
  have hcard : (U.recovered.family.unionCells.card : ℝ) ≤ (E.card : ℝ) := by
    exact_mod_cast card_le_card U.recovered.union_subset_E
  have hsquare : (U.recovered.family.unionCells.card : ℝ)^2 ≤ (E.card : ℝ)^2 :=
    pow_le_pow_left₀ (Nat.cast_nonneg _) hcard 2
  have hcap : capCoefficient (k:=k+1) (width:=width) d Cball =
      geometricFactor k width baseRadius d*L := cap_factorization k width baseRadius d L
  rw [hcap] at henergy
  refine ⟨rho,hrho,hlower,?_⟩
  calc
    _ = c₀*(kappa width B theta alpha)^5*(geometricFactor k width baseRadius d*L)⁻¹*
          rho^r*δ^(d-d'+1+eps)*(outputSupport U.selection.retained).card := by
      dsimp only [c,L]
      simp only [div_eq_mul_inv,mul_inv_rev]
      ring
    _ ≤ (U.recovered.family.unionCells.card : ℝ)^2 := henergy
    _ ≤ (E.card : ℝ)^2 := hsquare

end
end KakeyaFormal.OriginalPivotEnergy

#print axioms KakeyaFormal.OriginalPivotEnergy.geometricFactor_pos
#print axioms KakeyaFormal.OriginalPivotEnergy.cap_factorization
#print axioms KakeyaFormal.OriginalPivotEnergy.construct
