import OriginalPivotSlabs
import GenericMarkedPivotSelection

/-! Actual original marked pruning, recovery, output selection and selected slabs
for an explicitly admissible pivot radius. The radius is never compared with the
product choice. No logarithmic conditioning budgets are imposed. -/
namespace KakeyaFormal.AdmissiblePivotSlabs
open Finset TransverseAngles LegalAngleSamples ActualLabelSelection AngleFiberSelection
open MarkedPruningAssembly PivotSelectionBudgets PivotOutputLowerBound
open OriginalPivotSlabs (cutoff pruned spatial_coefficient_ge_one)
open scoped BigOperators
noncomputable section
open Classical

/-- The original geometric and marked data, without log-conditioning premises. -/
structure Hypotheses {n M : ℕ} (F : TubeFamily n M) (E : Finset (Cell n))
    (marks : Fin M → Finset (Cell n))
    (δ A lam xi B theta width baseRadius m alpha : ℝ) : Prop where
  scale_pos : 0 < δ
  scale_le_one : δ ≤ 1
  cap_coefficient : 1 ≤ A
  density_pos : 0 < lam
  marked_fraction_pos : 0 < xi
  count_pos : 0 < M
  two_ends_coefficient : 1 ≤ B
  angular_radius_pos : 0 < theta
  angular_radius_le_one : theta ≤ 1
  cover : ∀ i, F.shade i ⊆ E
  admissible : F.Admissible width δ
  separated : F.Separated δ
  bounded : F.Bounded baseRadius
  cap_bound : F.CapBound δ m A
  comparable : F.Comparable δ lam
  marks_subset : ∀ i, marks i ⊆ F.shade i
  marked_mass : xi*lam*(M : ℝ)/δ ≤ ∑ i, ((marks i).card : ℝ)
  marked_broad : ∀ z ∈ DensityBroadnessRecovery.cells marks,
    ∀ v : Space n, ‖v‖=1 →
      (((incident (MarkedSubsetSamples.markedFamily F marks) z).filter
        (fun i => projectiveDistance (F.tube i).direction v < theta)).card : ℝ) ≤
          ((incident (MarkedSubsetSamples.markedFamily F marks) z).card : ℝ)/10
  two_ends : ∀ i x r, δ ≤ r → r ≤ 1 →
    (((F.shade i).filter (fun z => dist (cellCenter δ z) x ≤ r)).card : ℝ) ≤
      B*r^alpha*((F.shade i).card : ℝ)


/-- Actual recovered selection, with original M, lambda and E. -/
theorem recovered_selection {k M : ℕ} {F O : TubeFamily (k+2) M}
    {marks : Fin M → Finset (Cell (k+2))} {E : Finset (Cell (k+2))}
    {δ lam xi width R m A B alpha theta kap : ℝ}
    (G : RecoveredInput F O marks E δ lam xi width R m A B alpha theta)
    (hδ : 0 < δ) (hδ1 : δ ≤ 1) (hlam : 0 < lam) (hxi : 0 < xi) (hM : 0 < M)
    (hw : (1:ℝ)/12 ≤ width) (hk : 0 < kap) (hk1 : kap ≤ 1)
    (hangle : 2*kap ≤ theta) (hradius : (2*width+1)*kap ≤ 1)
    (hlegal : (2*B)*((2*width+1)*kap)^alpha ≤ 1/16)
    (hsmall : (6*width/kap)*δ ≤ 1/2) :
    ∃ S : SampleSystem G.family G.family.unionCells δ G.density kap width,
    ∃ P : Selection S hk (by linarith : 0 ≤ width) G.admissible,
      let σ := ((2^P.level:ℕ):ℝ)*δ
      lam^2/(2048*LegalSampleOutputs.outputConstant (k+2) width) < σ ∧
      σ ≤ fiberCoefficient (k+2) width/kap ∧
      (outputCoefficient k width/65536)*kap^(5*(k+1))*xi^2*lam^8*(M : ℝ)^2/
        (σ^2*δ^4*(pivotLog δ)^3*(E.card : ℝ)) ≤ ((outputSupport P.retained).card : ℝ) := by
  have hw0 : 0 ≤ width := by linarith
  have hI : 0 < xi*lam*(M : ℝ)/(8*δ) := by positivity
  have hH : (G.family.unionCells.card : ℝ) ≤ E.card := by exact_mod_cast card_le_card G.union_subset_E
  obtain ⟨S,P,hlo,hhi,hQ⟩ := GenericMarkedPivotSelection.construct G.family G.marks G.family.unionCells
    hδ G.density_pos hw hk hk1 hangle hI G.comparison_pos G.admissible G.comparable
    G.separated G.marks_subset G.marked_mass hH (fun z _ v hv => G.marked_broad z v hv) G.two_ends hradius hlegal hsmall
  have hdensity : lam/2 ≤ G.density := by
    rcases G.density_choice with h | h
    · rw [h]
    · rw [h]; linarith
  let σ := ((2^P.level:ℕ):ℝ)*δ
  have hσ : 0 < σ := by
    have hh : (0:ℝ) < (2^P.level:ℕ) := by exact_mod_cast pow_pos (by omega : 0 < (2:ℕ)) P.level
    dsimp [σ]
    positivity
  have hlog := zero_lt_one.trans_le (pivotLog_ge_one hδ hδ1)
  have hC := LegalSampleOutputs.outputConstant_pos (k+2) hw0
  have hQcoef := outputCoefficient_pos k hw0
  refine ⟨S,P,?_,hhi,?_⟩
  · have hpow := pow_le_pow_left₀ (by positivity : 0 ≤ lam/2) hdensity 2
    have hh := div_le_div_of_nonneg_right hpow (by positivity : 0 ≤ 512*LegalSampleOutputs.outputConstant (k+2) width)
    have hid : lam^2/(2048*LegalSampleOutputs.outputConstant (k+2) width)=
        (lam/2)^2/(512*LegalSampleOutputs.outputConstant (k+2) width) := by field_simp; ring
    exact (hid ▸ hh).trans_lt hlo
  · calc
      _ = (outputCoefficient k width/16)*kap^(5*(k+1))*(lam/2)^6*
          (xi*lam*(M : ℝ)/(8*δ))^2/(σ^2*δ^2*(pivotLog δ)^3*(E.card : ℝ)) := by
        field_simp
        ring
      _ ≤ (outputCoefficient k width/16)*kap^(5*(k+1))*G.density^6*
          (xi*lam*(M : ℝ)/(8*δ))^2/(σ^2*δ^2*(pivotLog δ)^3*(E.card : ℝ)) := by
        gcongr
      _ ≤ _ := hQ


structure Package {k M : ℕ} (F : TubeFamily (k+2) M) (E : Finset (Cell (k+2)))
    (marks : Fin M → Finset (Cell (k+2)))
    (K δ A lam xi B theta width baseRadius m d p eps alpha kap : ℝ) where
  scale_pos : 0 < δ
  depth : ℕ
  depth_bound : (depth : ℝ) ≤ Real.log (1/δ)/Real.log 2
  geometry : PivotGeometryScale.Tests (k+2) δ kap width
  width_nonneg : 0 ≤ width
  kappa_pos : 0 < kap
  kappa_le_one : kap ≤ 1
  tubes_eq : (pruned F E K δ A lam xi m d p eps depth).tube=F.tube
  full_subset : ∀ i, (pruned F E K δ A lam xi m d p eps depth).shade i ⊆ F.shade i
  pruned_union_subset : (pruned F E K δ A lam xi m d p eps depth).unionCells ⊆ E
  deletion : δ*∑ i, ((F.shade i \ (pruned F E K δ A lam xi m d p eps depth).shade i).card : ℝ) ≤
    (xi/100)*lam*(M : ℝ)
  small_radius : ∀ x : Space (k+2), ∀ r : ℝ, δ ≤ r → r ≤ 1 →
    ((BallPruning.ballCells (pruned F E K δ A lam xi m d p eps depth).unionCells δ x r).card : ℝ) ≤
      (BallPruning.coverConstant (k+2) 1*(2:ℝ)^d*
        cutoff K E δ A lam xi m d p eps M depth)*(r/δ)^d
  recovered : RecoveredInput F (pruned F E K δ A lam xi m d p eps depth) marks E
    δ lam xi width baseRadius m A B alpha theta
  samples : SampleSystem recovered.family recovered.family.unionCells δ recovered.density
    kap width
  selection : Selection samples kappa_pos width_nonneg recovered.admissible
  lines : ∀ q : SelectedOutputPairs.Index selection, SelectedOutputSlabs.LineData selection q
  sigma_lower : lam^2/(2048*LegalSampleOutputs.outputConstant (k+2) width) <
    ((2^selection.level:ℕ):ℝ)*δ
  sigma_upper : ((2^selection.level:ℕ):ℝ)*δ ≤
    fiberCoefficient (k+2) width/kap
  output_lower : (outputCoefficient k width/65536)*kap^(5*(k+1))*
    xi^2*lam^8*(M : ℝ)^2/
      ((((2^selection.level:ℕ):ℝ)*δ)^2*δ^4*(pivotLog δ)^3*(E.card : ℝ)) ≤
        ((outputSupport selection.retained).card : ℝ)
  normalized_spatial : ∀ x : Space (k+2), ∀ r : ℝ, δ/(1+2*width) ≤ r →
    ((recovered.family.unionCells.filter
      (fun z => dist (cellCenter (δ/(1+2*width)) z) x ≤ r)).card : ℝ) ≤
      (PrunedGraphLift.spatialConstant (k+2) width baseRadius d*
        cutoff K E δ A lam xi m d p eps M depth)*(r/(δ/(1+2*width)))^d
  normalized_coefficient_ge_one : 1 ≤
    PrunedGraphLift.spatialConstant (k+2) width baseRadius d*
      cutoff K E δ A lam xi m d p eps M depth
  graph_coefficient_ge_one : 1 ≤
    (PrunedGraphLift.spatialConstant (k+2) width baseRadius d*
      cutoff K E δ A lam xi m d p eps M depth)*
        (16+2*(2*width+((k+2:ℕ):ℝ)/2))^d

/-- The same actual original pruning and all selected slabs, with a supplied
admissible radius. K is chosen before the radius, concentration parameters and
configuration. Every count and spatial conclusion is constructed internally. -/
theorem construct {k : ℕ} {m d p : ℝ}
    (hbase : DiscreteEstimate (k+2) m d p) (hm : 0 ≤ m) (hp : 1 ≤ p) (hd : 0 ≤ d)
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
  obtain ⟨K,hK,hprune⟩ := MarkedPruningAssembly.construct hbase hm hp hd width baseRadius hw0 eps heps
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
    (hbase : DiscreteEstimate (k+2) m d p) (hm : 0 ≤ m) (hp : 1 ≤ p) (hd : 0 ≤ d)
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
end KakeyaFormal.AdmissiblePivotSlabs
