import SpatialMarkedGroups
import AngularRestrictedMeasurable

/-! Original-grid population of actual spatial pieces. Their measurable full
unions are exactly common normalized unions of the corresponding OLD cells.
Only the proved physical spatial overlap is used; no sampled-cell overlap is
assumed. -/
namespace KakeyaFormal.SpatialGridPopulation
open Finset MeasureTheory GridShadingMeasure WidthNormalization SpatialMarkedPartition
open AngularSeedPieces AngularRestrictedRefinement
open scoped BigOperators ENNReal
noncomputable section
open Classical

/-- The old grid cells of one actual tube-label fiber. -/
def boxCells {n M : ℕ} {γ : Type*} [DecidableEq γ]
    (F : TubeFamily n M) (lab : Fin M → γ) (q : γ) : Finset (Cell n) :=
  (SpatialMarkedPartition.family F lab q).unionCells

/-- Each measurable spatial full union is precisely the same common
normalized union of its old cells, including the half-open boundaries. -/
theorem box_full_union {n M : ℕ} {γ : Type*} [DecidableEq γ]
    (F : TubeFamily n M) (lab : Fin M → γ) (q : γ) (δ W : ℝ) :
    (⋃ i, SpatialMarkedPartition.Full (GridMarked.shading F δ W) lab q i) =
      normalizedSet W (cellUnion δ (boxCells F lab q)) := by
  have hh := congrArg (normalizedSet W)
    (GridShadingMeasure.family_union (SpatialMarkedPartition.family F lab q) δ)
  simpa only [normalizedSet,Set.image_iUnion,SpatialMarkedPartition.Full,
    MeasurableMarkedSelection.reindex,GridMarked.shading,SpatialMarkedPartition.family,
    MeasurableMarkedSelection.family,boxCells] using hh

/-- All old box cells belong to the old input full union. -/
theorem boxCells_subset {n M : ℕ} {γ : Type*} [DecidableEq γ]
    (F : TubeFamily n M) (lab : Fin M → γ) (q : γ) : boxCells F lab q ⊆ F.unionCells := by
  intro z hz
  obtain ⟨i,_,hi⟩ := mem_biUnion.mp hz
  exact F.shade_subset_union _ hi

/-- The actual physical overlap bound cancels one common positive cell-volume
factor, yielding the original-grid count bound across ALL spatial labels. -/
theorem all_box_counts {k M : ℕ} (F : TubeFamily (k+1) M) (u : Space (k+1))
    {δ tau width angular W : ℝ} (hδ : 0 < δ) (hW : 0 < W)
    (hu : ‖u‖=1) (htau : 0 < tau) (hδtau : δ ≤ tau) (hw : 0 ≤ width) (ha : 0 ≤ angular)
    (hlocal : ∀ i, projectiveDistance (F.tube i).direction u ≤ angular*tau)
    (hcarrier : ∀ i, GridMarked.shading F δ W i ⊆ (F.tube i).carrier (width*δ)) :
    let lab := ActualSpatialMarked.label F u tau
    (∑ q : ↥(labels lab), ((boxCells F lab q.val).card:ℝ)) ≤
      (ActualSpatialMarked.overlapConstant k width angular:ℝ)*(F.unionCells.card:ℝ) := by
  intro lab
  have hh := ActualSpatialMarked.full_union_volume F u (GridMarked.shading F δ W)
    hu htau hδtau hw ha hlocal hcarrier
    (fun i => normalized_measurable hW (cellUnion_measurable δ (F.shade i)))
  simp_rw [box_full_union,grid_mass _ hδ hW] at hh
  rw [show (⋃ i, GridMarked.shading F δ W i) =
      (⋃ i, normalizedSet W (cellUnion δ (F.shade i))) from rfl,
    grid_union_mass F hδ hW] at hh
  have hid (a : ℝ) : δ^(k+1)*a/W^(k+1) = (δ^(k+1)/W^(k+1))*a := by ring
  simp_rw [hid] at hh
  rw [← mul_sum] at hh
  apply le_of_mul_le_mul_left (a:=δ^(k+1)/W^(k+1)) _ (by positivity)
  convert hh using 1 <;> first | rfl | ring

/-- Keep any actual subcollection, including ALL good boxes, with the same
old-grid count bound. No selection of a preferred spatial box is made. -/
theorem box_counts {k M : ℕ} (F : TubeFamily (k+1) M) (u : Space (k+1))
    {δ tau width angular W : ℝ} (hδ : 0 < δ) (hW : 0 < W)
    (hu : ‖u‖=1) (htau : 0 < tau) (hδtau : δ ≤ tau) (hw : 0 ≤ width) (ha : 0 ≤ angular)
    (hlocal : ∀ i, projectiveDistance (F.tube i).direction u ≤ angular*tau)
    (hcarrier : ∀ i, GridMarked.shading F δ W i ⊆ (F.tube i).carrier (width*δ))
    (Q : Finset (Cell k)) (hQ : Q ⊆ labels (ActualSpatialMarked.label F u tau)) :
    (∑ q ∈ Q, ((boxCells F (ActualSpatialMarked.label F u tau) q).card:ℝ)) ≤
      (ActualSpatialMarked.overlapConstant k width angular:ℝ)*(F.unionCells.card:ℝ) := by
  have hs : (∑ q ∈ Q, ((boxCells F (ActualSpatialMarked.label F u tau) q).card:ℝ)) ≤
      ∑ q ∈ labels (ActualSpatialMarked.label F u tau),
        ((boxCells F (ActualSpatialMarked.label F u tau) q).card:ℝ) :=
    sum_le_sum_of_subset_of_nonneg hQ (fun _ _ _ => Nat.cast_nonneg _)
  have he : (∑ q ∈ labels (ActualSpatialMarked.label F u tau),
      ((boxCells F (ActualSpatialMarked.label F u tau) q).card:ℝ)) =
      ∑ q : ↥(labels (ActualSpatialMarked.label F u tau)),
        ((boxCells F (ActualSpatialMarked.label F u tau) q.val).card:ℝ) :=
    sum_subtype _ (fun _ => Iff.rfl) _
  rw [he] at hs
  exact hs.trans (all_box_counts F u hδ hW hu htau hδtau hw ha hlocal hcarrier)

/-- Actual spatial labels of the refined whole-Ref measurable family. -/
def refinedLabel {k M : ℕ} {F : TubeFamily (k+1) M} {δ beta lam B alpha : ℝ}
    {P : Pieces F δ beta} {g : Fin M} (V : Refinement P lam B alpha g) (width : ℝ) :
    Fin V.N → Cell k :=
  ActualSpatialMarked.label (AngularRestrictedMeasurable.family V width) (F.tube g).direction P.tau

/-- The actual old cells in a refined angular group's spatial box. -/
def refinedCells {k M : ℕ} {F : TubeFamily (k+1) M} {δ beta lam B alpha : ℝ}
    {P : Pieces F δ beta} {g : Fin M} (V : Refinement P lam B alpha g) (width : ℝ) (q : Cell k) :
    Finset (Cell (k+1)) := boxCells (AngularRestrictedMeasurable.family V width) (refinedLabel V width) q

/-- The precise measurable union identity for the actual refined Ref sets. -/
theorem refined_full_union {k M : ℕ} {F : TubeFamily (k+1) M} {δ beta lam B alpha : ℝ}
    {P : Pieces F δ beta} {g : Fin M} (V : Refinement P lam B alpha g) (width : ℝ) (q : Cell k) :
    (⋃ i, SpatialMarkedPartition.Full (AngularRestrictedMeasurable.Full V width) (refinedLabel V width) q i) =
      normalizedSet (WidthNormalization.widthFactor (k+1) width) (cellUnion δ (refinedCells V width q)) :=
  box_full_union (AngularRestrictedMeasurable.family V width) (refinedLabel V width) q δ _

/-- Every actual good spatial subcollection of a refined angular group is
controlled by that group's OLD restricted cells, with a dimension-only loss. -/
theorem refined_box_counts {k M : ℕ} {F : TubeFamily (k+1) M} {δ beta lam B alpha width : ℝ}
    {P : Pieces F δ beta} {g : Fin M} (V : Refinement P lam B alpha g)
    (hg : g ∈ P.groups) (hδ : 0 < δ) (hadm : F.Admissible width δ)
    (Q : Finset (Cell k)) (hQ : Q ⊆ labels (refinedLabel V width)) :
    (∑ q ∈ Q, ((refinedCells V width q).card:ℝ)) ≤
      (ActualSpatialMarked.overlapConstant k 1 3:ℝ)*((P.family g).unionCells.card:ℝ) := by
  let H := AngularRestrictedMeasurable.family V width
  have hlocal : ∀ i, projectiveDistance (H.tube i).direction (F.tube g).direction ≤ 3*P.tau := by
    intro i
    change projectiveDistance (V.family.tube i).direction (F.tube g).direction ≤ 3*P.tau
    rw [(V.full_exact i).1]
    exact P.family_cap hg (V.index i)
  have hcarrier : ∀ i, GridMarked.shading H δ (widthFactor (k+1) width) i ⊆
      (H.tube i).carrier (1*δ) := by
    intro i
    simpa only [one_mul,H,GridMarked.shading,AngularRestrictedMeasurable.Full,
      AngularRestrictedMeasurable.family,GridMarked.family] using AngularRestrictedMeasurable.carrier V hδ hadm i
  have hh := box_counts H (F.tube g).direction hδ (widthFactor_pos (k+1) width)
    (F.tube g).unit_direction (hδ.trans_le P.lower_scale) P.lower_scale
    (by norm_num) (by norm_num) hlocal hcarrier Q hQ
  have hcard : (H.unionCells.card:ℝ) ≤ ((P.family g).unionCells.card:ℝ) := by
    exact_mod_cast card_le_card V.union_subset
  exact hh.trans (mul_le_mul_of_nonneg_left hcard (Nat.cast_nonneg _))

/-- Sum original spatial-box populations over every retained angular group.
The resulting tau^(-beta) is ONLY the original angular-piece overlap; there
is no assumption about overlap of new sampled cubes or their pullbacks. -/
theorem sum_refined_box_counts {k M : ℕ} {F : TubeFamily (k+1) M}
    {δ beta lam B alpha width : ℝ} (P : Pieces F δ beta)
    (hδ : 0 < δ) (hadm : F.Admissible width δ)
    (V : ∀ g : ↥(P.keptGroups lam), Refinement P lam B alpha g.val)
    (Q : ∀ _g : ↥(P.keptGroups lam), Finset (Cell k))
    (hQ : ∀ g, Q g ⊆ labels (refinedLabel (V g) width)) :
    (∑ g : ↥(P.keptGroups lam), ∑ q ∈ Q g, ((refinedCells (V g) width q).card:ℝ)) ≤
      (ActualSpatialMarked.overlapConstant k 1 3:ℝ)*(2*P.tau^(-beta)*(F.unionCells.card:ℝ)) := by
  have hh : (∑ g : ↥(P.keptGroups lam), ∑ q ∈ Q g, ((refinedCells (V g) width q).card:ℝ)) ≤
      (ActualSpatialMarked.overlapConstant k 1 3:ℝ)*
        ∑ g : ↥(P.keptGroups lam), ((P.family g.val).unionCells.card:ℝ) := by
    rw [mul_sum]
    apply sum_le_sum
    intro g _
    have hg : g.val ∈ P.groups := AngularGroupPruning.kept_subset P.groups P.shading _ g.property
    exact refined_box_counts (V g) hg hδ hadm (Q g) (hQ g)
  have hsum := AngularPiecePopulation.sum_old_unions (lam:=lam) P
  have he : (∑ g ∈ P.keptGroups lam, ((P.family g).unionCells.card:ℝ)) =
      ∑ g : ↥(P.keptGroups lam), ((P.family g.val).unionCells.card:ℝ) :=
    sum_subtype _ (fun _ => Iff.rfl) _
  rw [he] at hsum
  exact hh.trans (mul_le_mul_of_nonneg_left hsum (Nat.cast_nonneg _))

/-- In particular all actual sufficiently marked boxes can be used at once.
Their defining mass filter supplies the subcollection condition internally. -/
theorem sum_good_refined_box_counts {k M : ℕ} {F : TubeFamily (k+1) M}
    {δ beta lam B alpha width : ℝ} (P : Pieces F δ beta)
    (hδ : 0 < δ) (hadm : F.Admissible width δ)
    (V : ∀ g : ↥(P.keptGroups lam), Refinement P lam B alpha g.val)
    (eta mass : ↥(P.keptGroups lam) → ℝ) :
    (∑ g : ↥(P.keptGroups lam), ∑ q ∈
      SpatialMarkedGroups.good volume (AngularRestrictedMeasurable.Marks (V g) width)
        (refinedLabel (V g) width) (ActualSpatialMarked.overlapConstant k 1 3:ℝ) (eta g) (mass g),
      ((refinedCells (V g) width q).card:ℝ)) ≤
      (ActualSpatialMarked.overlapConstant k 1 3:ℝ)*(2*P.tau^(-beta)*(F.unionCells.card:ℝ)) :=
  sum_refined_box_counts P hδ hadm V _ (fun _ => filter_subset _ _)

end
end KakeyaFormal.SpatialGridPopulation
