import SpatialGridPopulation
import AnisotropicSamplingRetention
import MeasurableToDiscrete
import TransformedGridSupport

/-! Every sufficiently marked spatial box of an actual refined angular group
has a constructed anisotropic sampling input. All boxes are retained, and each
new full set stays inside the common image of its literal original grid cells.
The physical density upper bound is derived from an explicit fixed width test. -/
namespace KakeyaFormal.AngularSpatialSampling
open Finset MeasureTheory AngularSeedPieces AngularRestrictedRefinement
open WidthNormalization GridShadingMeasure SpatialMarkedPartition SpatialAngular
open scoped BigOperators ENNReal
noncomputable section
open Classical

variable {k M : ℕ} {F : TubeFamily (k+1) M} {δ beta lam B alpha : ℝ}
variable {P : Pieces F δ beta} {g : Fin M}

def physicalDensity (V : Refinement P lam B alpha g) (width : ℝ) : ℝ :=
  V.density/(widthFactor (k+1) width)^(k+1)

def markedRatio (V : Refinement P lam B alpha g) : ℝ := 1/(4*(V.depth+1:ℕ))

def endsConstant (_V : Refinement P lam B alpha g) (width : ℝ) : ℝ :=
  (((B*(4/P.eta))*(1+((k+1:ℕ):ℝ)/2)^alpha)*(widthFactor (k+1) width)^alpha)

def broadConstant (V : Refinement P lam B alpha g) : ℝ :=
  ((broadCoefficient k beta*(8/P.eta))*(2*(V.depth+1:ℕ)))

def spatialConstant (k : ℕ) : ℝ := ActualSpatialMarked.overlapConstant k 1 3

def boxes (V : Refinement P lam B alpha g) (width : ℝ) : Finset (Cell k) :=
  SpatialMarkedGroups.good volume (AngularRestrictedMeasurable.Marks V width)
    (SpatialGridPopulation.refinedLabel V width) (spatialConstant k) (markedRatio V)
    (physicalDensity V width*δ^k)

def boxFull (V : Refinement P lam B alpha g) (width : ℝ) (q : Cell k) :=
  SpatialMarkedPartition.Full (AngularRestrictedMeasurable.Full V width)
    (SpatialGridPopulation.refinedLabel V width) q

def boxMarks (V : Refinement P lam B alpha g) (width : ℝ) (q : Cell k) :=
  SpatialMarkedPartition.Marks (AngularRestrictedMeasurable.Marks V width)
    (SpatialGridPopulation.refinedLabel V width) (spatialConstant k) q

def boxFamily (V : Refinement P lam B alpha g) (width : ℝ) (q : Cell k) :=
  SpatialMarkedPartition.family (AngularRestrictedMeasurable.family V width)
    (SpatialGridPopulation.refinedLabel V width) q

def effectiveRatio (V : Refinement P lam B alpha g) : ℝ :=
  AnisotropicSamplingInput.retention k 3 (markedRatio V/4)

/-- The exact original tube index of a refined measurable reference. -/
def originalIndex (V : Refinement P lam B alpha g) (i : Fin V.N) : Fin M :=
  AngularGroupRestriction.index (P.shading g) (V.index i)

theorem originalIndex_injective (V : Refinement P lam B alpha g) :
    Function.Injective (originalIndex V) :=
  (AngularGroupRestriction.index_injective _).comp V.index_injective

theorem tube_exact (V : Refinement P lam B alpha g) (width : ℝ) (i : Fin V.N) :
    (AngularRestrictedMeasurable.family V width).tube i =
      normalizedTube (F.tube (originalIndex V i)) (widthFactor (k+1) width) := by
  change normalizedTube (V.family.tube i) _ = _
  rw [(V.full_exact i).1]
  rfl

/-- Direction and location hypotheses follow from the SAME composed original
index. No geometric hypothesis on a selected box is supplied. -/
theorem refined_geometry (V : Refinement P lam B alpha g) {width R m A : ℝ}
    (hg : g ∈ P.groups) (hR : 0 ≤ R) (hsep : F.Separated δ)
    (hbounded : F.Bounded R) (hcap : F.CapBound δ m A) :
    (AngularRestrictedMeasurable.family V width).Separated δ ∧
    (AngularRestrictedMeasurable.family V width).Bounded R ∧
    (AngularRestrictedMeasurable.family V width).CapBound δ m A ∧
    (∀ i, projectiveDistance ((AngularRestrictedMeasurable.family V width).tube i).direction
      (F.tube g).direction ≤ 3*P.tau) := by
  let H := GridMarked.family F (widthFactor (k+1) width)
  have hHs : H.Separated δ := hsep
  have hHc : H.CapBound δ m A := hcap
  have hHb : H.Bounded R := fun i => MeasurableToDiscrete.normalized_base_bound _
    (widthFactor_ge_one _ _) hR (hbounded i)
  obtain ⟨hs,hb,hc⟩ := DiscreteMeasurable.injective_tube_restriction H
    (AngularRestrictedMeasurable.family V width) (originalIndex V) (originalIndex_injective V)
    (tube_exact V width) hHs hHb hHc
  refine ⟨hs,hb,hc,?_⟩
  intro i
  change projectiveDistance (V.family.tube i).direction (F.tube g).direction ≤ 3*P.tau
  rw [(V.full_exact i).1]
  exact P.family_cap hg (V.index i)

theorem physicalDensity_pos (V : Refinement P lam B alpha g) (width : ℝ) :
    0 < physicalDensity V width := div_pos V.density_pos (pow_pos (widthFactor_pos _ _) _)

/-- V.density can reach 2*lam. The fixed denominator test is used explicitly. -/
theorem physicalDensity_le_one (V : Refinement P lam B alpha g) {width : ℝ}
    (hlam : lam ≤ 1) (hW : 2 ≤ (widthFactor (k+1) width)^(k+1)) :
    physicalDensity V width ≤ 1 := by
  apply (div_le_one (pow_pos (widthFactor_pos _ _) _)).mpr
  have hh : 2*lam ≤ (widthFactor (k+1) width)^(k+1) := by linarith
  exact V.density_upper.trans hh

theorem markedRatio_pos (V : Refinement P lam B alpha g) : 0 < markedRatio V := by
  unfold markedRatio
  positivity

theorem markedRatio_le_one (V : Refinement P lam B alpha g) : markedRatio V ≤ 1 := by
  unfold markedRatio
  apply (div_le_one (by positivity)).mpr
  have hh : (1:ℝ) ≤ (V.depth+1:ℕ) := by exact_mod_cast Nat.succ_le_succ (Nat.zero_le _)
  linarith

theorem endsConstant_ge_one (V : Refinement P lam B alpha g) (width : ℝ)
    (hB : 1 ≤ B) (ha : 0 ≤ alpha) : 1 ≤ endsConstant V width := by
  have hr : 1 ≤ 4/P.eta := (le_div_iff₀ P.eta_pos).mpr (by linarith [P.eta_le_one])
  have h1 : 1 ≤ (1+((k+1:ℕ):ℝ)/2)^alpha := Real.one_le_rpow (by have hh : (0:ℝ) ≤ (k+1:ℕ) := Nat.cast_nonneg _; linarith) ha
  have h2 : 1 ≤ (widthFactor (k+1) width)^alpha := Real.one_le_rpow (widthFactor_ge_one _ _) ha
  have hh : 1 ≤ B*(4/P.eta) := by nlinarith
  have hh1 : 1 ≤ (B*(4/P.eta))*(1+((k+1:ℕ):ℝ)/2)^alpha := by nlinarith
  unfold endsConstant
  nlinarith

theorem broadConstant_pos (V : Refinement P lam B alpha g) : 0 < broadConstant V := by
  unfold broadConstant
  positivity [broadCoefficient_pos k beta,P.eta_pos]

theorem spatialConstant_pos (k : ℕ) : 0 < spatialConstant k := by
  unfold spatialConstant
  exact_mod_cast ActualSpatialMarked.overlapConstant_pos k 1 3

/-- The actual refined marked fraction gives the physical mass budget used
by every spatial partition, with the common volume normalization unchanged. -/
theorem marked_budget (V : Refinement P lam B alpha g) (width : ℝ) (hδ : 0 < δ) :
    markedRatio V*(physicalDensity V width*δ^k)*(V.N:ℝ) ≤
      ∑ i, (volume : Measure (Space (k+1))).real (AngularRestrictedMeasurable.Marks V width i) := by
  have hh : (physicalDensity V width*δ^k)*(V.N:ℝ) ≤
      ∑ i, (volume : Measure (Space (k+1))).real (AngularRestrictedMeasurable.Full V width i) := by
    simpa [mul_comm,physicalDensity] using sum_le_sum (fun i (_hi : i ∈ (univ:Finset (Fin V.N))) =>
      (AngularRestrictedMeasurable.full_density V width hδ i).1)
  have hdiv := div_le_div_of_nonneg_right hh (by positivity : (0:ℝ) ≤ 4*(V.depth+1:ℕ))
  calc
    _ = ((physicalDensity V width*δ^k)*(V.N:ℝ))/(4*(V.depth+1:ℕ)) := by unfold markedRatio; ring
    _ ≤ _ := hdiv
    _ ≤ _ := AngularRestrictedMeasurable.marked_fraction V width hδ

/-- Exact per-box target constants, including the fixed spatial overlap in
marked broadness and the actual common-box dimensions. -/
abbrev BoxOutput (V : Refinement P lam B alpha g) (width R m A : ℝ) (q : Cell k) :=
  AnisotropicSamplingRetention.Output (boxFull V width q) (F.tube g).direction q δ P.tau 1
    (AnisotropicJointGeometry.baseBound 3 (R+2) ((k:ℝ)+4)) 3 (physicalDensity V width)
    (effectiveRatio V) (endsConstant V width) alpha beta
    (broadConstant V*(4*spatialConstant k)) m (AnisotropicJointGeometry.capFactor k 3 m*A)


/-- Actual spatial selection data. All boxes of the defining good filter are
kept; the mass and population inequalities are sums over that whole set. -/
structure SpatialData (V : Refinement P lam B alpha g) (width R : ℝ) : Prop where
  nonempty : (boxes V width).Nonempty
  population : markedRatio V*(V.N:ℝ)/4 ≤
    ∑ q ∈ boxes V width, ((indices (SpatialGridPopulation.refinedLabel V width) q).card:ℝ)
  marked_mass : markedRatio V*(physicalDensity V width*δ^k)*(V.N:ℝ)/2 ≤
    ∑ q ∈ boxes V width, SpatialMarkedGroups.markedMass volume
      (AngularRestrictedMeasurable.Marks V width) (SpatialGridPopulation.refinedLabel V width)
      (spatialConstant k) q
  box_population : ∀ q ∈ boxes V width, 0 < (indices (SpatialGridPopulation.refinedLabel V width) q).card
  box_marked_mass : ∀ q ∈ boxes V width,
    (markedRatio V/4)*(physicalDensity V width*δ^k)*
      ((indices (SpatialGridPopulation.refinedLabel V width) q).card:ℝ) ≤
        ∑ i, (volume : Measure (Space (k+1))).real (boxMarks V width q i)
  box_nested : ∀ q ∈ boxes V width, ∀ i, boxMarks V width q i ⊆ boxFull V width q i
  common_box : ∀ q ∈ boxes V width, ∀ i, ((boxFamily V width q).tube i).base ∈
    parallelBox (F.tube g).direction P.tau q (R+2) ((k:ℝ)+4)
  broad : ∀ q ∈ boxes V width, ∀ x, AngularDecomposition.Broad (boxFamily V width q)
    (univ.filter (fun i => x ∈ boxMarks V width q i)) δ beta P.tau
      (broadConstant V*(4*spatialConstant k))

/-- Derive the physical box geometry and marked budgets directly from the
actual refined references and original family geometry. -/
theorem spatial_data (V : Refinement P lam B alpha g) {width R m A : ℝ}
    (hg : g ∈ P.groups) (hδ : 0 < δ) (hR : 0 ≤ R)
    (hadm : F.Admissible width δ) (hsep : F.Separated δ)
    (hbounded : F.Bounded R) (hcap : F.CapBound δ m A) : SpatialData V width R := by
  obtain ⟨_hs,hb,_hc,hl⟩ := refined_geometry V hg hR hsep hbounded hcap (width:=width)
  have hcarrier : ∀ i, AngularRestrictedMeasurable.Full V width i ⊆
      ((AngularRestrictedMeasurable.family V width).tube i).carrier (1*δ) := by
    simpa only [one_mul] using AngularRestrictedMeasurable.carrier V hδ hadm
  have hupper : ∀ i, (volume : Measure (Space (k+1))).real
      (AngularRestrictedMeasurable.Full V width i) ≤ 2*(physicalDensity V width*δ^k) := by
    intro i
    convert (AngularRestrictedMeasurable.full_density V width hδ i).2 using 1
    unfold physicalDensity
    ring
  have hh := SpatialMarkedGroups.construct (AngularRestrictedMeasurable.family V width)
    (F.tube g).direction (AngularRestrictedMeasurable.Full V width) (AngularRestrictedMeasurable.Marks V width)
    (F.tube g).unit_direction hδ P.lower_scale (P.lower_scale.trans P.upper_scale)
    (by norm_num : (0:ℝ)≤1) (by norm_num : (0:ℝ)≤3) hb
    (markedRatio_pos V) (mul_pos (physicalDensity_pos V width) (pow_pos hδ k))
    (broadConstant_pos V).le V.population_pos hl hcarrier
    (AngularRestrictedMeasurable.marks_subset_full V width)
    (AngularRestrictedMeasurable.measurable V width).2 hupper (marked_budget V width hδ)
    (AngularRestrictedMeasurable.marked_broad V width hδ)
  obtain ⟨hne,hpop,hmass,hq⟩ := hh
  refine ⟨hne,hpop,hmass,fun q h => (hq q h).1,fun q h => (hq q h).2.1,
    fun q h => (hq q h).2.2.2.1,?_,fun q h => (hq q h).2.2.2.2.2.1⟩
  intro q h i
  have hbq := (hq q h).2.2.2.2.1 i
  convert hbq using 1 <;> congr 1 <;> ring

/-- Finite full shadings in a spatial box remain exactly comparable at the
unscaled original density V.density. Their cell labels are not resampled. -/
theorem box_comparable (V : Refinement P lam B alpha g) (width : ℝ) (q : Cell k) :
    (boxFamily V width q).Comparable δ V.density := by
  intro i
  exact V.comparable (MeasurableMarkedSelection.index
    (indices (SpatialGridPopulation.refinedLabel V width) q) i)

/-- Every actual spatial subfamily inherits the original angular cap,
separation, and real-cap bound through injective indices. -/
theorem box_geometry (V : Refinement P lam B alpha g) {width R m A : ℝ}
    (hg : g ∈ P.groups) (hR : 0 ≤ R) (hsep : F.Separated δ)
    (hbounded : F.Bounded R) (hcap : F.CapBound δ m A) (q : Cell k) :
    (boxFamily V width q).Separated δ ∧ (boxFamily V width q).CapBound δ m A ∧
      (∀ i, projectiveDistance ((boxFamily V width q).tube i).direction (F.tube g).direction ≤ 3*P.tau) := by
  obtain ⟨hs,_hb,hc,hl⟩ := refined_geometry V hg hR hsep hbounded hcap (width:=width)
  exact ActualSpatialMarked.family_geometry (AngularRestrictedMeasurable.family V width)
    (F.tube g).direction hs hc hl q

/-- Each box receives the actual anisotropic shared-segment, color and
marked-weighted density selection. Broadness uses the proved proportional
marked filter, and full two ends is inherited from the unchanged references. -/
theorem box_output (V : Refinement P lam B alpha g) {width R m A : ℝ}
    (hg : g ∈ P.groups) (hδ : 0 < δ) (hR : 0 ≤ R) (hlam : lam ≤ 1)
    (hW : 2 ≤ (widthFactor (k+1) width)^(k+1))
    (hB : 1 ≤ B) (ha : 0 ≤ alpha) (hbeta : 0 < beta) (hm : 0 ≤ m) (hA : 0 ≤ A)
    (hadm : F.Admissible width δ) (hsep : F.Separated δ)
    (hbounded : F.Bounded R) (hcap : F.CapBound δ m A)
    (T : SpatialData V width R) (q : Cell k) (hq : q ∈ boxes V width) :
    Nonempty (BoxOutput V width R m A q) := by
  obtain ⟨hs,hc,hl⟩ := box_geometry V hg hR hsep hbounded hcap q (width:=width)
  have hsub := T.box_nested q hq
  have hFull : ∀ i, MeasurableSet (boxFull V width q i) :=
    fun i => (AngularRestrictedMeasurable.measurable V width).1 _
  have hMarks : ∀ i, MeasurableSet (boxMarks V width q i) :=
    SpatialMarkedPartition.marks_measurable _ _ _ q (AngularRestrictedMeasurable.measurable V width).2
  have hcarrier : ∀ i, boxFull V width q i ⊆ ((boxFamily V width q).tube i).carrier (1*δ) := by
    intro i
    simpa only [one_mul,boxFull,boxFamily,SpatialMarkedPartition.Full,SpatialMarkedPartition.family,
      MeasurableMarkedSelection.reindex,MeasurableMarkedSelection.family] using AngularRestrictedMeasurable.carrier V hδ hadm
      (MeasurableMarkedSelection.index (indices (SpatialGridPopulation.refinedLabel V width) q) i)
  have hupper : ∀ i, (volume : Measure (Space (k+1))).real (boxFull V width q i) ≤
      2*(physicalDensity V width*δ^k) := by
    intro i
    convert (AngularRestrictedMeasurable.full_density V width hδ
      (MeasurableMarkedSelection.index (indices (SpatialGridPopulation.refinedLabel V width) q) i)).2 using 1 <;>
      first | rfl | (unfold physicalDensity; ring)
  have hends : ∀ i x r, δ ≤ r → (volume : Measure (Space (k+1))).real
      (boxFull V width q i ∩ Metric.closedBall x r) ≤
        endsConstant V width*r^alpha*(volume : Measure (Space (k+1))).real (boxFull V width q i) := by
    intro i
    exact AngularRestrictedMeasurable.two_ends V width hδ hB ha
      (MeasurableMarkedSelection.index (indices (SpatialGridPopulation.refinedLabel V width) q) i)
  exact AnisotropicSamplingRetention.construct (boxFamily V width q) (F.tube g).direction
    (boxFull V width q) (boxMarks V width q) (F.tube g).unit_direction hδ P.lower_scale P.upper_scale
    (by norm_num) (by norm_num) (div_pos (markedRatio_pos V) (by norm_num))
    (by have hh := markedRatio_le_one V; linarith : markedRatio V/4≤1)
    (physicalDensity_pos V width) (physicalDensity_le_one V hlam hW) (endsConstant_ge_one V width hB ha)
    ha hbeta (by positivity [broadConstant_pos V,spatialConstant_pos k]) hm hA (T.box_population q hq)
    q hFull hMarks hsub hcarrier hl hs hc (T.common_box q hq) hupper (T.box_marked_mass q hq) hends (T.broad q hq)


/-- Each original full shading of the box lies in the literal common
normalized union used as the old support in the later high-density estimate. -/
theorem box_full_support (V : Refinement P lam B alpha g) (width : ℝ) (q : Cell k) :
    ∀ i, boxFull V width q i ⊆ normalizedSet (widthFactor (k+1) width)
      (cellUnion δ (SpatialGridPopulation.refinedCells V width q)) := by
  intro i x hx
  rw [← SpatialGridPopulation.refined_full_union]
  exact Set.mem_iUnion.mpr ⟨i,hx⟩

/-- Finite box shadings and the recorded old-cell union use exactly the same
labels, despite the physical normalization of their tube bases. -/
theorem box_cells_eq (V : Refinement P lam B alpha g) (width : ℝ) (q : Cell k) :
    (boxFamily V width q).unionCells = SpatialGridPopulation.refinedCells V width q := rfl

/-- The new full shadings lie in the common map of the SAME old finite cell
union for this box. Different output tubes do not receive separate maps. -/
theorem old_cell_support (V : Refinement P lam B alpha g) {width R m A : ℝ}
    (q : Cell k) (O : BoxOutput V width R m A q) : ∀ i, O.full i ⊆
      (TransformedGridSupport.pieceMap (F.tube g).direction P.tau (widthFactor (k+1) width) q) ''
        cellUnion δ (SpatialGridPopulation.refinedCells V width q) := by
  intro i x hx
  obtain ⟨y,hy,hxy⟩ := O.contained i hx
  have hunion : y ∈ ⋃ j, boxFull V width q j := Set.mem_iUnion.mpr ⟨O.index i,hy⟩
  change y ∈ ⋃ j, SpatialMarkedPartition.Full (AngularRestrictedMeasurable.Full V width)
    (SpatialGridPopulation.refinedLabel V width) q j at hunion
  rw [SpatialGridPopulation.refined_full_union] at hunion
  obtain ⟨z,hz,hzy⟩ := hunion
  refine ⟨z,hz,?_⟩
  exact (congrArg (normalizeBox (F.tube g).direction P.tau q) hzy).trans hxy

/-- The simultaneous actual outputs, retaining ALL good spatial boxes and
their original-grid population bound. No sampling cube overlap is assumed. -/
structure Package (V : Refinement P lam B alpha g) (width R m A : ℝ) where
  spatial : SpatialData V width R
  output : ∀ q : ↥(boxes V width), BoxOutput V width R m A q.val
  old_support : ∀ q : ↥(boxes V width), ∀ i, (output q).full i ⊆
    (TransformedGridSupport.pieceMap (F.tube g).direction P.tau (widthFactor (k+1) width) q.val) ''
      cellUnion δ (SpatialGridPopulation.refinedCells V width q.val)
  old_count : (∑ q ∈ boxes V width, ((SpatialGridPopulation.refinedCells V width q).card:ℝ)) ≤
    spatialConstant k*((P.family g).unionCells.card:ℝ)

/-- Actual refined angular data and original family geometry construct every
spatial sampling output. The fixed width test makes physical density at most
one; all remaining normalization, color, box and population data is derived. -/
theorem construct (V : Refinement P lam B alpha g) {width R m A : ℝ}
    (hg : g ∈ P.groups) (hδ : 0 < δ) (hR : 0 ≤ R) (hlam : lam ≤ 1)
    (hW : 2 ≤ (widthFactor (k+1) width)^(k+1))
    (hB : 1 ≤ B) (ha : 0 ≤ alpha) (hbeta : 0 < beta) (hm : 0 ≤ m) (hA : 0 ≤ A)
    (hadm : F.Admissible width δ) (hsep : F.Separated δ)
    (hbounded : F.Bounded R) (hcap : F.CapBound δ m A) :
    Nonempty (Package V width R m A) := by
  let T := spatial_data V hg hδ hR hadm hsep hbounded hcap
  have hO (q : ↥(boxes V width)) : Nonempty (BoxOutput V width R m A q.val) :=
    box_output V hg hδ hR hlam hW hB ha hbeta hm hA hadm hsep hbounded hcap T q.val q.property
  let O (q : ↥(boxes V width)) : BoxOutput V width R m A q.val := Classical.choice (hO q)
  exact ⟨{
    spatial := T
    output := O
    old_support := fun q => old_cell_support V q.val (O q)
    old_count := SpatialGridPopulation.refined_box_counts V hg hδ hadm (boxes V width) (filter_subset _ _)
  }⟩

/-- Across every retained angular group and every good box, the old cell
population loses only the already proved spatial constant and angular overlap. -/
theorem total_old_count (P : Pieces F δ beta) {width : ℝ}
    (hδ : 0 < δ) (hadm : F.Admissible width δ)
    (V : ∀ g : ↥(P.keptGroups lam), Refinement P lam B alpha g.val) :
    (∑ g : ↥(P.keptGroups lam), ∑ q ∈ boxes (V g) width,
      ((SpatialGridPopulation.refinedCells (V g) width q).card:ℝ)) ≤
        spatialConstant k*(2*P.tau^(-beta)*(F.unionCells.card:ℝ)) :=
  SpatialGridPopulation.sum_good_refined_box_counts P hδ hadm V (fun g => markedRatio (V g))
    (fun g => physicalDensity (V g) width*δ^k)

end
end KakeyaFormal.AngularSpatialSampling
