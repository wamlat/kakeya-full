import UniformPrunedPivotSelection
import SelectedOutputSlabs
import RecoveredNormalizedBall

/-! Original marked configuration to actual simultaneous selected lift slabs.
The returned data retains the original spatial pruning and its common-scale
transport; no selected-pair, selected-cell or normalized ball premise is supplied. -/
namespace KakeyaFormal.OriginalPivotSlabs
open Finset TransverseAngles LegalAngleSamples ActualLabelSelection AngleFiberSelection
open MarkedPruningAssembly PivotSelectionBudgets PivotOutputLowerBound
open scoped BigOperators
noncomputable section
open Classical

/-- Original, visible hypotheses. The fixed coefficients and logarithmic
exponents belong to the theorem's outer parameters. -/
structure Hypotheses {n M : ℕ} (F : TubeFamily n M) (E : Finset (Cell n))
    (marks : Fin M → Finset (Cell n))
    (δ₀ δ A lam xi B theta width baseRadius m alpha B₀ K₀ b q : ℝ) : Prop where
  scale_pos : 0 < δ
  scale_small : δ ≤ δ₀
  cap_coefficient : 1 ≤ A
  density_pos : 0 < lam
  marked_fraction_pos : 0 < xi
  count_pos : 0 < M
  two_ends_coefficient : 1 ≤ B
  angular_radius_pos : 0 < theta
  angular_radius_le_one : theta ≤ 1
  two_ends_budget : B ≤ B₀*(Real.log (2/δ))^b
  angular_budget : theta⁻¹ ≤ K₀*(Real.log (2/δ))^q
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

/-- The literal threshold from marked-fraction spatial pruning. -/
abbrev cutoff {n : ℕ} (K : ℝ) (E : Finset (Cell n))
    (δ A lam xi m d p eps : ℝ) (M J : ℕ) : ℝ :=
  max 1 (K*(E.card : ℝ)*A*δ^(d-m-eps)*
    ((xi/100)/((J : ℝ)+1))^(-(p+1))*lam^(-p)/(M : ℝ))

abbrev pruned {n M : ℕ} (F : TubeFamily n M) (E : Finset (Cell n))
    (K δ A lam xi m d p eps : ℝ) (J : ℕ) : TubeFamily n M :=
  PrunedIncidence.family F E δ (cutoff K E δ A lam xi m d p eps M J) d J

abbrev kappa (width B theta alpha : ℝ) : ℝ :=
  PivotKappa.choice width (2*B) theta⁻¹ alpha 1

/-- The spatial coefficient itself, before applying the graph chart, is at
least one. This is the exact normalization required by grouped pruning. -/
theorem spatial_coefficient_ge_one (n : ℕ) {width baseRadius d L : ℝ}
    (hd : 0 ≤ d) (hL : 1 ≤ L) :
    1 ≤ PrunedGraphLift.spatialConstant n width baseRadius d*L := by
  have hcover : 1 ≤ BallPruning.coverConstant n 1 := by
    have h1 := one_le_pow₀ (n := n) (show (1:ℝ) ≤ 5 by norm_num)
    have h2 := one_le_pow₀ (n := n)
      (show (1:ℝ) ≤ 1+1+(n:ℝ)/2 by have hn := Nat.cast_nonneg (α := ℝ) n; linarith)
    dsimp [BallPruning.coverConstant]
    nlinarith
  have hpow := Real.one_le_rpow (show (1:ℝ) ≤ 2 by norm_num) hd
  have hsp : 1 ≤ PrunedGraphLift.spatialConstant n width baseRadius d :=
    (show 1 ≤ BallPruning.coverConstant n 1*(2:ℝ)^d by nlinarith).trans (le_max_left _ _)
  nlinarith

/-- A single coherent actual output package. Original and normalized scales
are explicit, as are the original M/E in the output-population inequality. -/
structure Package {k M : ℕ} (F : TubeFamily (k+2) M) (E : Finset (Cell (k+2)))
    (marks : Fin M → Finset (Cell (k+2)))
    (K δ A lam xi B theta width baseRadius m d p eps alpha : ℝ) where
  scale_pos : 0 < δ
  depth : ℕ
  depth_bound : (depth : ℝ) ≤ Real.log (1/δ)/Real.log 2
  geometry : PivotGeometryScale.Tests (k+2) δ (kappa width B theta alpha) width
  width_nonneg : 0 ≤ width
  kappa_pos : 0 < kappa width B theta alpha
  kappa_le_one : kappa width B theta alpha ≤ 1
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
    (kappa width B theta alpha) width
  selection : Selection samples kappa_pos width_nonneg recovered.admissible
  lines : ∀ q : SelectedOutputPairs.Index selection, SelectedOutputSlabs.LineData selection q
  sigma_lower : lam^2/(2048*LegalSampleOutputs.outputConstant (k+2) width) <
    ((2^selection.level:ℕ):ℝ)*δ
  sigma_upper : ((2^selection.level:ℕ):ℝ)*δ ≤
    fiberCoefficient (k+2) width/kappa width B theta alpha
  output_lower : (outputCoefficient k width/65536)*(kappa width B theta alpha)^(5*(k+1))*
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

/-- Uniform original-input construction. All slab cells, their exact original
representatives and their common normalized spatial bound are constructed
from the original configuration. -/
theorem construct {k : ℕ} {m d p : ℝ}
    (hbase : DiscreteEstimate (k+2) m d p) (hm : 0 ≤ m) (hp : 1 ≤ p) (hd : 0 ≤ d)
    (width baseRadius : ℝ) (hw : (1:ℝ)/12 ≤ width) (eps : ℝ) (heps : 0 < eps)
    (B₀ K₀ alpha b q : ℝ) (hB₀ : 0 < B₀) (hK₀ : 0 < K₀)
    (ha : 0 < alpha) (hb : 0 ≤ b) (hq : 0 ≤ q) :
    ∃ K : ℝ, 0 < K ∧ ∃ δ₀ : ℝ, 0 < δ₀ ∧ δ₀ ≤ 1 ∧
      ∀ {M : ℕ} (F : TubeFamily (k+2) M) (E : Finset (Cell (k+2)))
      (marks : Fin M → Finset (Cell (k+2))) {δ A lam xi B theta : ℝ},
      Hypotheses F E marks δ₀ δ A lam xi B theta width baseRadius m alpha B₀ K₀ b q →
      Nonempty (Package F E marks K δ A lam xi B theta width baseRadius m d p eps alpha) := by
  obtain ⟨K,hK,δ₀,hδ₀,hδ₀1,hconstruct⟩ := UniformPrunedPivotSelection.construct
    hbase hm hp hd width baseRadius hw eps heps B₀ K₀ alpha b q hB₀ hK₀ ha hb hq
  refine ⟨K,hK,δ₀,hδ₀,hδ₀1,?_⟩
  intro M F E marks δ A lam xi B theta h
  obtain ⟨htests,J,hdepth,htube,hsub,hOE,hdel,hball,G,hkap,S,P,hlo,hhi,hout⟩ :=
    hconstruct F E marks h.scale_pos h.scale_small h.cap_coefficient h.density_pos
      h.marked_fraction_pos h.count_pos h.two_ends_coefficient h.angular_radius_pos
      h.angular_radius_le_one h.two_ends_budget h.angular_budget h.cover h.admissible
      h.separated h.bounded h.cap_bound h.comparable h.marks_subset h.marked_mass
      h.marked_broad h.two_ends
  have hw0 : 0 ≤ width := by linarith
  have hkap1 : kappa width B theta alpha ≤ 1 := by
    have hh := (MarkedSubsetSamples.fixed_radius_choice hw0
      (by linarith [h.two_ends_coefficient] : 1 ≤ 2*B) ha
      h.angular_radius_pos h.angular_radius_le_one).2.1
    exact hh.trans (by norm_num)
  let D := SelectedOutputSlabs.selectedLine P h.scale_pos htests.original_scale_le_one
    hkap1 htests.selected_slab_small
  have hL : 1 ≤ cutoff K E δ A lam xi m d p eps M J := le_max_left _ _
  have hnormalized := RecoveredNormalizedBall.recovered_ball_bound F E marks G h.scale_pos
    htests.original_scale_le_one hw0 (zero_le_one.trans hL) hd h.admissible h.bounded hball
  refine ⟨{
    scale_pos := h.scale_pos
    depth := J
    depth_bound := hdepth
    geometry := htests
    width_nonneg := hw0
    kappa_pos := hkap
    kappa_le_one := hkap1
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

end
end KakeyaFormal.OriginalPivotSlabs

#print axioms KakeyaFormal.OriginalPivotSlabs.spatial_coefficient_ge_one
#print axioms KakeyaFormal.OriginalPivotSlabs.construct
