import LocalAngularLowDensityOriginal
import AngularSpatialBudgets

/-! The sparse local angular estimate on the SAME constructed spatial package.
All original-box geometric, measurable, marked and logarithmic inputs are
derived; only the actual branch tests and original family hypotheses remain. -/
namespace KakeyaFormal.AngularBoxLowDensity
open Finset MeasureTheory AngularSeedPieces AngularRestrictedRefinement AngularSpatialSampling
open WidthNormalization GridShadingMeasure SpatialMarkedPartition
open scoped BigOperators ENNReal
noncomputable section
open Classical

theorem spatialConstant_ge_one (k : ℕ) : 1 ≤ spatialConstant k := by
  change (1:ℝ) ≤ (ActualSpatialMarked.overlapConstant k 1 3:ℝ)
  exact_mod_cast (Nat.one_le_iff_ne_zero.mpr (ne_of_gt (ActualSpatialMarked.overlapConstant_pos k 1 3)))

/-- The literal marked broadness constant is already at least one; no
replacement of it, or of the actual marked reference rows, is needed. -/
theorem box_broad_ge_one {k M : ℕ} {F : TubeFamily (k+1) M}
    {δ beta lam B alpha : ℝ} {P : Pieces F δ beta} {g : Fin M}
    (V : Refinement P lam B alpha g) (hbeta : 0 ≤ beta) :
    1 ≤ AngularSpatialSampling.broadConstant V*(4*spatialConstant k) := by
  have hb : 1 ≤ AngularRestrictedRefinement.broadCoefficient k beta :=
    AngularSeedHairbrush.broadConstant_ge_one k hbeta
  have hr : 1 ≤ 8/P.eta := (le_div_iff₀ P.eta_pos).mpr (by linarith [P.eta_le_one])
  have hdep : (1:ℝ) ≤ 2*(V.depth+1:ℕ) := by
    have hh : (1:ℝ) ≤ (V.depth+1:ℕ) := by exact_mod_cast Nat.succ_le_succ (Nat.zero_le _)
    linarith
  have hs : 1 ≤ 4*spatialConstant k := by linarith [spatialConstant_ge_one k]
  exact one_le_mul_of_one_le_of_one_le
    (one_le_mul_of_one_le_of_one_le (one_le_mul_of_one_le_of_one_le hb hr) hdep) hs

/-- Uniform low-density old-cell estimate for every actual good box. The
physical density and box population are the original ones, before the joint
segment/color/measured selection; the tested output is exactly U.output q. -/
theorem construct (k : ℕ) (width R B alpha beta m D C eps a : ℝ)
    (hR : 0 ≤ R) (hB : 1 ≤ B) (halpha : 0 < alpha) (hbeta : 0 < beta)
    (hm : 1 ≤ m) (hC : 2 ≤ C) (heps : 0 < eps) (ha : 1 ≤ a)
    (hmargin : 0 < (m+3)/2-D+(C-2)/3)
    (hW : 2 ≤ (widthFactor (k+2) width)^(k+2)) :
    ∃ c : ℝ, 0 < c ∧ ∀ {M : ℕ} {δ lam A : ℝ} (F : TubeFamily (k+2) M)
      (P : Pieces F δ beta) {g : Fin M} (V : Refinement P lam B alpha g)
      (U : Package V width R m A),
      g ∈ P.groups → 0 < δ → lam ≤ 1 → 1 ≤ Real.log (2/δ) → 1 ≤ A →
      F.Admissible width δ → F.Separated δ → F.Bounded R → F.CapBound δ m A →
      (δ/P.tau)^a ≤ δ → ∀ q : ↥(boxes V width),
      (U.output q).density ≤ (δ/P.tau)^((1:ℝ)/3) →
      c*A⁻¹*(δ/P.tau)^(m-D+eps)*(physicalDensity V width)^C*
        ((indices (SpatialGridPopulation.refinedLabel V width) q.val).card:ℝ) ≤
          ((SpatialGridPopulation.refinedCells V width q.val).card:ℝ) := by
  obtain ⟨heff,hBc,hKc,_⟩ := AngularSpatialBudgets.coefficients_pos (k+1) width beta alpha (zero_lt_one.trans_le hB)
  have hdepth : 0 < AngularRefinementBudgets.depthFactor (k+1) :=
    (AngularRefinementBudgets.constants_pos (k+1)).2.2
  obtain ⟨c,hc,hmain⟩ := LocalAngularLowDensityOriginal.original_parameters k
    (angular:=3) (eta₀:=1/(16*AngularRefinementBudgets.depthFactor (k+1)))
    (B₀:=AngularSpatialBudgets.endsCoefficient (k+1) width B alpha)
    (K₀:=AngularSpatialBudgets.broadCoefficient (k+1) beta)
    (bLog:=1) (kLog:=2) (qLog:=1) (e₀:=AngularSpatialBudgets.effectiveCoefficient (k+1)) (xLog:=1)
    (by norm_num) (by positivity) halpha hbeta hBc hKc (by norm_num) (by norm_num)
    (by norm_num) heff (by norm_num) ha hm hC heps hmargin
  refine ⟨c,hc,?_⟩
  intro M δ lam A F P g V U hg hδ hlam hL hA hadm hsep hbounded hcap hscale q hsmall
  have hFull : ∀ i, MeasurableSet (boxFull V width q.val i) :=
    fun i => (AngularRestrictedMeasurable.measurable V width).1 _
  have hMarks : ∀ i, MeasurableSet (boxMarks V width q.val i) :=
    SpatialMarkedPartition.marks_measurable _ _ _ q.val (AngularRestrictedMeasurable.measurable V width).2
  have hcarrier : ∀ i, boxFull V width q.val i ⊆ ((boxFamily V width q.val).tube i).carrier δ := by
    intro i
    exact AngularRestrictedMeasurable.carrier V hδ hadm
      (MeasurableMarkedSelection.index (indices (SpatialGridPopulation.refinedLabel V width) q.val) i)
  have hupper : ∀ i, (volume : Measure (Space (k+2))).real (boxFull V width q.val i) ≤
      2*physicalDensity V width*δ^(k+1) := by
    intro i
    exact (AngularRestrictedMeasurable.full_density V width hδ
      (MeasurableMarkedSelection.index (indices (SpatialGridPopulation.refinedLabel V width) q.val) i)).2
  have hmass : (markedRatio V/4)*physicalDensity V width*δ^(k+1)*
      ((indices (SpatialGridPopulation.refinedLabel V width) q.val).card:ℝ) ≤
        ∑ i, (volume : Measure (Space (k+2))).real (boxMarks V width q.val i) := by
    convert U.spatial.box_marked_mass q.val q.property using 1; first | rfl | ring
  have hends : ∀ i x r, δ ≤ r → r ≤ 1 →
      (volume : Measure (Space (k+2))).real (boxFull V width q.val i ∩ Metric.closedBall x r) ≤
        AngularSpatialSampling.endsConstant V width*r^alpha*
          (volume : Measure (Space (k+2))).real (boxFull V width q.val i) := by
    intro i x r hr _
    exact AngularRestrictedMeasurable.two_ends V width hδ hB halpha.le
      (MeasurableMarkedSelection.index (indices (SpatialGridPopulation.refinedLabel V width) q.val) i) x r hr
  have hetaBudget : (1/(16*AngularRefinementBudgets.depthFactor (k+1)))*(Real.log (2/δ))^(-(1:ℝ)) ≤
      markedRatio V/4 := by
    have hh := div_le_div_of_nonneg_right (AngularRefinementBudgets.marked_ratio_budget V hδ hL)
      (by norm_num : (0:ℝ)≤4)
    simp only [markedRatio,div_eq_mul_inv,mul_inv_rev] at hh ⊢
    convert hh using 1 <;> first | rfl | ring
  have hsupport : (⋃ i, boxFull V width q.val i) ⊆ normalizedSet (widthFactor (k+2) width)
      (cellUnion δ (SpatialGridPopulation.refinedCells V width q.val)) :=
    Set.iUnion_subset (box_full_support V width q.val)
  obtain ⟨hs,hc,hl⟩ := box_geometry V hg hR hsep hbounded hcap q.val (width:=width)
  exact hmain (boxFamily V width q.val) (boxFull V width q.val) (boxMarks V width q.val)
    (F.tube g).direction q.val (SpatialGridPopulation.refinedCells V width q.val)
    (U.spatial.box_population q.val q.property) (F.tube g).unit_direction hδ P.lower_scale P.upper_scale
    (div_pos (markedRatio_pos V) (by norm_num)) (by linarith [markedRatio_le_one V])
    (physicalDensity_pos V width) (physicalDensity_le_one V hlam hW)
    (endsConstant_ge_one V width hB halpha.le) (box_broad_ge_one V hbeta.le) hA (widthFactor_ge_one _ _)
    hscale hFull hMarks (U.spatial.box_nested q.val q.property) hcarrier hl hs hc hupper hmass
    (U.spatial.broad q.val q.property) hends
    (AngularSpatialBudgets.ends_budget V width hδ hL (zero_le_one.trans hB))
    (AngularSpatialBudgets.broad_budget V hδ hL) hetaBudget hsupport (U.output q) hsmall
    (AngularSpatialBudgets.effective_budget V hδ hL)

end
end KakeyaFormal.AngularBoxLowDensity
