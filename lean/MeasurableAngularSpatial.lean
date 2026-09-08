import MeasurableAngularPieces
import SpatialMarkedPartition
import SpatialTubeCover

/-! Actual measurable angular and spatial pieces. Spatial families consist of
disjoint original tube indices. Their shadings are measurable subsets of the
same original shadings, and their full carriers lie in explicit finite-length
parallel tubes. The only loss depending on the mesh is the original angular
depth loss. All assertions hold pointwise, not merely almost everywhere. -/
namespace KakeyaFormal.MeasurableAngularSpatial
open MeasureTheory Set AngularDecomposition
open scoped ENNReal
noncomputable section
open Classical

variable {k M : ℕ} {F : TubeFamily (k+1) M}
  {Y : Fin M → Set (Space (k+1))} {δ beta : ℝ}

def angularFamily (P : MeasurableAngularPieces.Pieces F Y δ beta) (g : Fin M) :=
  MeasurableAngularGroups.family F (P.shading g)

def angularShading (P : MeasurableAngularPieces.Pieces F Y δ beta) (g : Fin M) :=
  MeasurableAngularGroups.compressed (P.shading g) (P.shading g)

def label (P : MeasurableAngularPieces.Pieces F Y δ beta) (g : Fin M) := fun i =>
  SpatialTubeCover.label (F.tube g).direction P.tau ((angularFamily P g).tube i)

def labels (P : MeasurableAngularPieces.Pieces F Y δ beta) (g : Fin M) := SpatialMarkedPartition.labels (label P g)

def population (P : MeasurableAngularPieces.Pieces F Y δ beta) (g : Fin M) (q : SpatialTubeCover.Label k) : ℕ :=
  (SpatialMarkedPartition.indices (label P g) q).card

def spatialConstant (k : ℕ) (width : ℝ) : ℕ :=
  SpatialTubeCover.overlapConstant k (2+width) ((k:ℝ)+width+3)

def family (P : MeasurableAngularPieces.Pieces F Y δ beta) (g : Fin M) (q : SpatialTubeCover.Label k) :
    TubeFamily (k+1) (population P g q) :=
  SpatialMarkedPartition.family (angularFamily P g) (label P g) q

def shading (P : MeasurableAngularPieces.Pieces F Y δ beta) (width : ℝ) (g : Fin M) (q : SpatialTubeCover.Label k) :
    Fin (population P g q) → Set (Space (k+1)) :=
  SpatialMarkedPartition.Marks (angularShading P g) (label P g) (spatialConstant k width) q

def originalIndex (P : MeasurableAngularPieces.Pieces F Y δ beta) (g : Fin M) (q : SpatialTubeCover.Label k)
    (i : Fin (population P g q)) : Fin M :=
  MeasurableAngularGroups.index (P.shading g)
    (MeasurableMarkedSelection.index (SpatialMarkedPartition.indices (label P g) q) i)

theorem originalIndex_injective (P : MeasurableAngularPieces.Pieces F Y δ beta) (g : Fin M) (q : SpatialTubeCover.Label k) :
    Function.Injective (originalIndex P g q) :=
  (MeasurableAngularGroups.index_injective _).comp (MeasurableMarkedSelection.index_injective _)

theorem tube_eq (P : MeasurableAngularPieces.Pieces F Y δ beta) (g : Fin M) (q : SpatialTubeCover.Label k)
    (i : Fin (population P g q)) : (family P g q).tube i = F.tube (originalIndex P g q i) := rfl

theorem original_assignment (P : MeasurableAngularPieces.Pieces F Y δ beta) (g : Fin M) (q : SpatialTubeCover.Label k)
    (i : Fin (population P g q)) : P.assign (originalIndex P g q i) = g :=
  P.unique g _ (MeasurableAngularGroups.index_nonempty _ _)

theorem original_label (P : MeasurableAngularPieces.Pieces F Y δ beta) (g : Fin M) (q : SpatialTubeCover.Label k)
    (i : Fin (population P g q)) :
    SpatialTubeCover.label (F.tube g).direction P.tau (F.tube (originalIndex P g q i)) = q :=
  SpatialMarkedPartition.index_label (label P g) q i

/-- Distinct angular/spatial groups contain disjoint original tube indices. -/
theorem groups_disjoint (P : MeasurableAngularPieces.Pieces F Y δ beta) (g h : Fin M) (q r : SpatialTubeCover.Label k)
    (i : Fin (population P g q)) (j : Fin (population P h r))
    (he : originalIndex P g q i = originalIndex P h r j) : g = h ∧ q = r := by
  have hg := (original_assignment P g q i).symm.trans
    ((congrArg P.assign he).trans (original_assignment P h r j))
  subst h
  exact ⟨rfl,(original_label P g q i).symm.trans
    ((congrArg (fun z => SpatialTubeCover.label (F.tube g).direction P.tau (F.tube z)) he).trans
      (original_label P g r j))⟩

theorem shading_subset_angular (P : MeasurableAngularPieces.Pieces F Y δ beta) (width : ℝ) (g : Fin M)
    (q : SpatialTubeCover.Label k) (i : Fin (population P g q)) :
    shading P width g q i ⊆ P.shading g (originalIndex P g q i) := Set.inter_subset_left

theorem shading_subset (P : MeasurableAngularPieces.Pieces F Y δ beta) (width : ℝ) (g : Fin M)
    (q : SpatialTubeCover.Label k) (i : Fin (population P g q)) :
    shading P width g q i ⊆ Y (originalIndex P g q i) :=
  (shading_subset_angular P width g q i).trans (P.subset g _)

theorem shading_measurable (P : MeasurableAngularPieces.Pieces F Y δ beta) (width : ℝ) (g : Fin M)
    (q : SpatialTubeCover.Label k) : ∀ i, MeasurableSet (shading P width g q i) :=
  SpatialMarkedPartition.marks_measurable _ _ _ _
    (MeasurableAngularGroups.compressed_measurable _ _ (P.measurable g))

theorem shading_finite (P : MeasurableAngularPieces.Pieces F Y δ beta) (width : ℝ) (g : Fin M)
    (q : SpatialTubeCover.Label k) (i : Fin (population P g q)) :
    volume (shading P width g q i) ≠ ∞ :=
  measure_ne_top_of_subset (shading_subset_angular P width g q i) (P.finite g _)

theorem union_subset (P : MeasurableAngularPieces.Pieces F Y δ beta) (width : ℝ) (g : Fin M) (q : SpatialTubeCover.Label k) :
    (⋃ i, shading P width g q i) ⊆ ⋃ i, Y i := by
  intro x hx
  obtain ⟨i,hi⟩ := mem_iUnion.mp hx
  exact mem_iUnion.mpr ⟨_,shading_subset P width g q i hi⟩

theorem separated (P : MeasurableAngularPieces.Pieces F Y δ beta) (g : Fin M) (q : SpatialTubeCover.Label k)
    {s : ℝ} (hsep : F.Separated s) : (family P g q).Separated s :=
  MeasurableMarkedSelection.family_separated _ _
    (MeasurableAngularGroups.family_separated F _ hsep)

theorem local_cap (P : MeasurableAngularPieces.Pieces F Y δ beta) (g : Fin M) (hg : g ∈ P.groups)
    (q : SpatialTubeCover.Label k) (i : Fin (population P g q)) :
    projectiveDistance ((family P g q).tube i).direction (F.tube g).direction ≤ 3*P.tau :=
  P.local_cap g hg _ (MeasurableAngularGroups.index_nonempty _ _)

/-- The complete original tube, including endpoint caps, has a finite spatial
container. This uses no bounded-base or bounded-region input. -/
theorem containing_box (P : MeasurableAngularPieces.Pieces F Y δ beta) (g : Fin M) (hg : g ∈ P.groups)
    (q : SpatialTubeCover.Label k) (i : Fin (population P g q))
    {width : ℝ} (hδ : 0 < δ) (hδ1 : δ ≤ 1) (hw : 0 ≤ width) :
    ((family P g q).tube i).carrier (width*δ) ⊆
      SpatialTubeCover.parallelBox (F.tube g).direction P.tau q
        (2+width) ((k:ℝ)+width+3) := by
  have hh := SpatialTubeCover.tube_in_box (F.tube g).direction (F.tube g).unit_direction
    ((family P g q).tube i) (hδ.trans_le P.lower_scale) P.lower_scale hδ1 hw
    (by norm_num : (0:ℝ)≤3) (local_cap P g hg q i)
  rwa [tube_eq,original_label] at hh

theorem containing_tube (P : MeasurableAngularPieces.Pieces F Y δ beta) (g : Fin M) (hg : g ∈ P.groups)
    (q : SpatialTubeCover.Label k) (i : Fin (population P g q))
    {width : ℝ} (hδ : 0 < δ) (hδ1 : δ ≤ 1) (hw : 0 ≤ width) :
    ((family P g q).tube i).carrier (width*δ) ⊆
      SamplingGeometry.lengthCarrier
        (SpatialTubeCover.containingTube (F.tube g).direction (F.tube g).unit_direction
          P.tau q (2+width)) (2*(2+width)) (((k:ℝ)+width+3)*P.tau) :=
  (containing_box P g hg q i hδ hδ1 hw).trans
    (SpatialTubeCover.box_in_length_carrier _ _ _ _ _ _)

theorem occupied_labels (P : MeasurableAngularPieces.Pieces F Y δ beta) (g : Fin M) (hg : g ∈ P.groups)
    {width : ℝ} (hδ : 0 < δ) (hδ1 : δ ≤ 1) (hw : 0 ≤ width)
    (hcarrier : ∀ i, Y i ⊆ (F.tube i).carrier (width*δ)) (x : Space (k+1)) :
    ((Finset.univ.filter (fun i => x ∈ angularShading P g i)).image (label P g)).card ≤
      spatialConstant k width := by
  apply SpatialTubeCover.occupied_labels (F.tube g).direction (F.tube g).unit_direction
    (angularFamily P g).tube _ x (hδ.trans_le P.lower_scale) P.lower_scale hδ1 hw
    (by norm_num : (0:ℝ)≤3)
  · intro i _
    exact P.local_cap g hg _ (MeasurableAngularGroups.index_nonempty _ _)
  · intro i hi
    exact hcarrier _ (P.subset g _ (Finset.mem_filter.mp hi).2)

theorem retained_mass (P : MeasurableAngularPieces.Pieces F Y δ beta) {width : ℝ}
    (hδ : 0 < δ) (hδ1 : δ ≤ 1) (hw : 0 ≤ width)
    (hcarrier : ∀ i, Y i ⊆ (F.tube i).carrier (width*δ)) :
    ((3/4:ℝ)*AngularSeedPieces.retentionRate k P.J)*(∑ i, volume.real (Y i)) ≤
      ∑ g ∈ P.groups, ∑ q ∈ labels P g, ∑ i, volume.real (shading P width g q i) := by
  have hh := mul_le_mul_of_nonneg_left P.retained (by norm_num : (0:ℝ)≤3/4)
  have hh' : ((3/4:ℝ)*AngularSeedPieces.retentionRate k P.J)*(∑ i, volume.real (Y i)) ≤
      ∑ g ∈ P.groups, (3/4:ℝ)*MeasurableAngularPruning.mass volume (P.shading g) := by
    calc
      _ ≤ (3/4:ℝ)*(∑ g ∈ P.groups, MeasurableAngularPruning.mass volume (P.shading g)) := by
        simpa only [mul_assoc] using hh
      _ = _ := Finset.mul_sum _ _ _
  apply hh'.trans
  apply Finset.sum_le_sum
  intro g hg
  have hs := SpatialMarkedPartition.marked_mass volume (angularShading P g) (label P g)
    (Nat.cast_pos.mpr (SpatialTubeCover.overlapConstant_pos k (2+width) ((k:ℝ)+width+3)))
    (MeasurableAngularGroups.compressed_measurable _ _ (P.measurable g))
    (MeasurableAngularGroups.compressed_finite volume _ _ (P.finite g))
    (fun x => Nat.cast_le.mpr (occupied_labels P g hg hδ hδ1 hw hcarrier x))
  rw [angularShading, MeasurableAngularGroups.mass_eq] at hs
  exact hs

theorem broad (P : MeasurableAngularPieces.Pieces F Y δ beta) {width : ℝ} (hδ : 0 < δ)
    (g : Fin M) (hg : g ∈ P.groups) (q : SpatialTubeCover.Label k) :
    ∀ x, Broad (family P g q) (Finset.univ.filter (fun i => x ∈ shading P width g q i))
      δ beta P.tau ((4:ℝ)^beta*(4*AngularSeedPieces.angularConstant k)*(4*spatialConstant k width)) :=
  SpatialMarkedPartition.marked_broad _ _ _ _ _ hδ.le (hδ.trans_le P.lower_scale)
    (by positivity [AngularSeedPieces.angularConstant_pos k])
    (MeasurableAngularGroups.family_broad F _ (fun x => P.broad x g hg))

theorem population_bound (P : MeasurableAngularPieces.Pieces F Y δ beta) :
    (∑ g ∈ P.groups, ∑ q ∈ labels P g, population P g q) ≤ M := by
  have he (g) : (∑ q ∈ labels P g, population P g q) =
      (MeasurableAngularGroups.active (P.shading g)).card :=
    SpatialMarkedPartition.population_partition (label P g)
  simp_rw [he]
  exact MeasurableAngularGroups.total_active_count P.groups P.shading P.assign P.unique

def occupied (P : MeasurableAngularPieces.Pieces F Y δ beta) (width : ℝ)
    (g : Fin M) (x : Space (k+1)) : Finset (SpatialTubeCover.Label k) :=
  (labels P g).filter (fun q => ∃ i, x ∈ shading P width g q i)

theorem spatial_overlap (P : MeasurableAngularPieces.Pieces F Y δ beta)
    (g : Fin M) (hg : g ∈ P.groups) {width : ℝ}
    (hδ : 0 < δ) (hδ1 : δ ≤ 1) (hw : 0 ≤ width)
    (hcarrier : ∀ i, Y i ⊆ (F.tube i).carrier (width*δ)) (x : Space (k+1)) :
    (occupied P width g x).card ≤ spatialConstant k width := by
  have hs : occupied P width g x ⊆
      (Finset.univ.filter (fun i => x ∈ angularShading P g i)).image (label P g) := by
    intro q hq
    obtain ⟨i,hi⟩ := (Finset.mem_filter.mp hq).2
    refine Finset.mem_image.mpr ⟨MeasurableMarkedSelection.index
      (SpatialMarkedPartition.indices (label P g) q) i, Finset.mem_filter.mpr ⟨Finset.mem_univ _,hi.1⟩,?_⟩
    exact SpatialMarkedPartition.index_label (label P g) q i
  exact (Finset.card_le_card hs).trans (occupied_labels P g hg hδ hδ1 hw hcarrier x)

/-- Actual overlap of the retained measurable subunions, summed over all
angular and spatial labels. The geometric spatial cost is independent of tau. -/
theorem total_overlap (P : MeasurableAngularPieces.Pieces F Y δ beta) {width : ℝ}
    (hδ : 0 < δ) (hδ1 : δ ≤ 1) (hw : 0 ≤ width)
    (hcarrier : ∀ i, Y i ⊆ (F.tube i).carrier (width*δ)) (x : Space (k+1)) :
    (∑ g ∈ P.groups, ((occupied P width g x).card:ℝ)) ≤
      (2*(spatialConstant k width:ℝ))*P.tau^(-beta) := by
  let A := P.groups.filter (fun g => ∃ i, x ∈ P.shading g i)
  have he : (∑ g ∈ P.groups, ((occupied P width g x).card:ℝ)) =
      ∑ g ∈ A, ((occupied P width g x).card:ℝ) := by
    symm
    apply Finset.sum_subset (Finset.filter_subset _ _)
    intro g hg hga
    have hnone : ¬∃ i, x ∈ P.shading g i := by simpa only [A,Finset.mem_filter,hg,true_and] using hga
    have hz : occupied P width g x = ∅ := by
      apply Finset.eq_empty_iff_forall_notMem.mpr
      intro q hq
      obtain ⟨i,hi⟩ := (Finset.mem_filter.mp hq).2
      exact hnone ⟨_,shading_subset_angular P width g q i hi⟩
    simp only [hz,Finset.card_empty,Nat.cast_zero]
  rw [he]
  have hs : (∑ g ∈ A, ((occupied P width g x).card:ℝ)) ≤ ∑ _g ∈ A, (spatialConstant k width:ℝ) :=
    Finset.sum_le_sum (fun g hg => Nat.cast_le.mpr
      (spatial_overlap P g (Finset.mem_filter.mp hg).1 hδ hδ1 hw hcarrier x))
  simp only [Finset.sum_const,nsmul_eq_mul] at hs
  have hh := mul_le_mul_of_nonneg_right (P.overlap x) (Nat.cast_nonneg (spatialConstant k width))
  exact hs.trans (by simpa only [A,mul_assoc,mul_comm,mul_left_comm] using hh)

end
end KakeyaFormal.MeasurableAngularSpatial
