import PositiveDensityPruning

/-! The admissible-radius actual selected-slab package for every positive base
density exponent. This reuses the frozen package and its geometric interfaces. -/
namespace KakeyaFormal.PositivePivotSlabs
open Finset TransverseAngles LegalAngleSamples ActualLabelSelection AngleFiberSelection
open MarkedPruningAssembly PivotSelectionBudgets PivotOutputLowerBound AdmissiblePivotSlabs
open OriginalPivotSlabs (cutoff pruned spatial_coefficient_ge_one)
open scoped BigOperators
noncomputable section
open Classical

/-- Construct every original pruning, marked recovery, output and slab datum
using the genuine positive-density coarse estimate. -/
theorem construct {k : ℕ} {m d p : ℝ}
    (hbase : DiscreteEstimate (k+2) m d p) (hm : 0 ≤ m) (hp : 0 < p) (hd : 0 ≤ d)
    (width baseRadius : ℝ) (hw : (1:ℝ)/12 ≤ width) (eps : ℝ) (heps : 0 < eps) :
    ∃ K : ℝ, 0 < K ∧
      ∀ {M : ℕ} (F : TubeFamily (k+2) M) (E : Finset (Cell (k+2)))
      (marks : Fin M → Finset (Cell (k+2))) {δ A lam xi B theta alpha kap : ℝ},
      Hypotheses F E marks δ A lam xi B theta width baseRadius m alpha →
      0 < kap → kap ≤ 1 → 2*kap ≤ theta → (2*width+1)*kap ≤ 1 →
      (2*B)*((2*width+1)*kap)^alpha ≤ 1/16 →
      PivotGeometryScale.Tests (k+2) δ kap width →
      Nonempty (Package F E marks K δ A lam xi B theta width baseRadius m d p eps alpha kap) := by
  have hw0 : 0 ≤ width := by linarith
  obtain ⟨K,hK,hprune⟩ := PositiveDensityPruning.marked_recovery hbase hm hp hd width baseRadius hw0 eps heps
  refine ⟨K,hK,?_⟩
  intro M F E marks δ A lam xi B theta alpha kap h hk hk1 hangle hradius hlegal htests
  obtain ⟨J,hdepth,htube,hsub,hOE,hdel,hball,⟨G⟩⟩ := hprune F E marks h.scale_pos h.scale_le_one
    h.cap_coefficient h.density_pos h.marked_fraction_pos h.count_pos
    (by linarith [h.two_ends_coefficient] : 0 ≤ B) h.cover h.admissible h.separated h.bounded
    h.cap_bound h.comparable h.marks_subset h.marked_mass h.marked_broad h.two_ends
  obtain ⟨S,P,hlo,hhi,hout⟩ := recovered_selection G h.scale_pos h.scale_le_one
    h.density_pos h.marked_fraction_pos h.count_pos hw hk hk1 hangle hradius hlegal htests.collision_small
  let D := SelectedOutputSlabs.selectedLine P h.scale_pos htests.original_scale_le_one
    hk1 htests.selected_slab_small
  have hL : 1 ≤ cutoff K E δ A lam xi m d p eps M J := le_max_left _ _
  have hnormalized := RecoveredNormalizedBall.recovered_ball_bound F E marks G h.scale_pos
    htests.original_scale_le_one hw0 (zero_le_one.trans hL) hd h.admissible h.bounded hball
  refine ⟨{
    scale_pos := h.scale_pos
    depth := J
    depth_bound := hdepth
    geometry := htests
    width_nonneg := hw0
    kappa_pos := hk
    kappa_le_one := hk1
    tubes_eq := htube
    full_subset := hsub
    pruned_union_subset := hOE
    deletion := hdel
    small_radius := hball
    recovered := G
    samples := S
    selection := P
    lines := D
    sigma_lower := hlo
    sigma_upper := hhi
    output_lower := hout
    normalized_spatial := hnormalized
    normalized_coefficient_ge_one := spatial_coefficient_ge_one (k+2) hd hL
    graph_coefficient_ge_one := RecoveredNormalizedBall.recovered_cap_coefficient_ge_one
      (k+2) hw0 hd hL }⟩

/-- The literal source minimum now supplies the entire original-input package.
Only its original twentieth-power scale cutoff is imposed; no B/theta log
budget, product-radius comparison or desired output/count premise remains. -/
theorem construct_source {k : ℕ} {m d p : ℝ}
    (hbase : DiscreteEstimate (k+2) m d p) (hm : 0 ≤ m) (hp : 0 < p) (hd : 0 ≤ d)
    (width baseRadius : ℝ) (hw : (1:ℝ)/12 ≤ width) (eps : ℝ) (heps : 0 < eps) :
    ∃ K : ℝ, 0 < K ∧
      ∀ {M : ℕ} (F : TubeFamily (k+2) M) (E : Finset (Cell (k+2)))
      (marks : Fin M → Finset (Cell (k+2))) {δ A lam xi B theta alpha : ℝ},
      Hypotheses F E marks δ A lam xi B theta width baseRadius m alpha → 0 < alpha →
      PivotGeometryScale.geometryConstant (k+2) width*(1+2*width)^20 ≤
        (1/δ)*(MinPivotKappa.sourceChoice width B alpha theta)^20 →
      Nonempty (Package F E marks K δ A lam xi B theta width baseRadius m d p eps alpha
        (MinPivotKappa.sourceChoice width B alpha theta)) := by
  obtain ⟨K,hK,hconstruct⟩ := construct hbase hm hp hd width baseRadius hw eps heps
  refine ⟨K,hK,?_⟩
  intro M F E marks δ A lam xi B theta alpha h ha hscale
  have hw0 : 0 ≤ width := by linarith
  obtain ⟨hk,hk100,hangle,hradius,hlegal⟩ := MinPivotKappa.source_admissible hw0
    h.two_ends_coefficient ha h.angular_radius_pos
  have hk1 : MinPivotKappa.sourceChoice width B alpha theta ≤ 1 := hk100.trans (by norm_num)
  exact hconstruct F E marks h hk hk1 hangle hradius hlegal
    (PivotGeometryScale.tests_of_original_twentieth (k+2) h.scale_pos hk hk1 hw0 hscale)


end
end KakeyaFormal.PositivePivotSlabs
