import MeasurableAngularDecomposition
import SpatialTubeLengths
import MeasurableSeedLengths

/-! Literal measurable angular-spatial decomposition with a fixed upper bound
on actual per-tube axis lengths. No spatial dilation, new grid, bounded-region
restriction, or replacement of the original shadings is used. -/
namespace KakeyaFormal.MeasurableAngularSpatialLengths
open MeasureTheory Set AngularDecomposition MeasurableAngularSpatial SpatialTubeLengths
open scoped ENNReal
noncomputable section
open Classical

variable {k M : ℕ} {F : TubeFamily (k+1) M}
  {Y : Fin M → Set (Space (k+1))} {δ beta width upperLength : ℝ}

theorem occupied_labels (P : MeasurableAngularPieces.Pieces F Y δ beta)
    (length : Fin M → ℝ) (g : Fin M) (hg : g ∈ P.groups)
    (hδ : 0 < δ) (hδ1 : δ ≤ 1) (hw : 0 ≤ width)
    (hL : ∀ i, length i ≤ upperLength)
    (hcarrier : ∀ i, Y i ⊆ SamplingGeometry.lengthCarrier (F.tube i) (length i) (width*δ))
    (x : Space (k+1)) :
    ((Finset.univ.filter (fun i => x ∈ angularShading P g i)).image (label P g)).card ≤
      spatialConstant k (coverWidth width upperLength) := by
  apply SpatialTubeCover.box_overlap (F.tube g).direction x (hδ.trans_le P.lower_scale)
  intro q hq
  obtain ⟨i,hi,rfl⟩ := Finset.mem_image.mp hq
  exact length_in_box (F.tube g).direction (F.tube g).unit_direction
    ((angularFamily P g).tube i) (hδ.trans_le P.lower_scale) P.lower_scale hδ1 hw (hL _)
    (P.local_cap g hg _ (MeasurableAngularGroups.index_nonempty _ _))
    (hcarrier _ (P.subset g _ (Finset.mem_filter.mp hi).2))

theorem containing_box (P : MeasurableAngularPieces.Pieces F Y δ beta)
    (length : Fin M → ℝ) (g : Fin M) (hg : g ∈ P.groups)
    (q : SpatialTubeCover.Label k) (i : Fin (population P g q))
    (hδ : 0 < δ) (hδ1 : δ ≤ 1) (hw : 0 ≤ width) (hL : ∀ i, length i ≤ upperLength) :
    SamplingGeometry.lengthCarrier ((family P g q).tube i)
      (length (originalIndex P g q i)) (width*δ) ⊆
      SpatialTubeCover.parallelBox (F.tube g).direction P.tau q
        (2+coverWidth width upperLength) ((k:ℝ)+coverWidth width upperLength+3) := by
  have hh := length_in_box (F.tube g).direction (F.tube g).unit_direction
    ((family P g q).tube i) (hδ.trans_le P.lower_scale) P.lower_scale hδ1 hw
    (hL (originalIndex P g q i)) (local_cap P g hg q i)
  rwa [tube_eq,original_label] at hh

theorem containing_tube (P : MeasurableAngularPieces.Pieces F Y δ beta)
    (length : Fin M → ℝ) (g : Fin M) (hg : g ∈ P.groups)
    (q : SpatialTubeCover.Label k) (i : Fin (population P g q))
    (hδ : 0 < δ) (hδ1 : δ ≤ 1) (hw : 0 ≤ width) (hL : ∀ i, length i ≤ upperLength) :
    SamplingGeometry.lengthCarrier ((family P g q).tube i)
      (length (originalIndex P g q i)) (width*δ) ⊆
      SamplingGeometry.lengthCarrier
        (SpatialTubeCover.containingTube (F.tube g).direction (F.tube g).unit_direction
          P.tau q (2+coverWidth width upperLength)) (2*(2+coverWidth width upperLength))
            (((k:ℝ)+coverWidth width upperLength+3)*P.tau) :=
  (containing_box P length g hg q i hδ hδ1 hw hL).trans
    (SpatialTubeCover.box_in_length_carrier _ _ _ _ _ _)

theorem retained_mass (P : MeasurableAngularPieces.Pieces F Y δ beta)
    (length : Fin M → ℝ) (hδ : 0 < δ) (hδ1 : δ ≤ 1) (hw : 0 ≤ width)
    (hL : ∀ i, length i ≤ upperLength)
    (hcarrier : ∀ i, Y i ⊆ SamplingGeometry.lengthCarrier (F.tube i) (length i) (width*δ)) :
    ((3/4:ℝ)*AngularSeedPieces.retentionRate k P.J)*(∑ i,volume.real (Y i)) ≤
      ∑ g ∈ P.groups, ∑ q ∈ labels P g, ∑ i,
        volume.real (shading P (coverWidth width upperLength) g q i) := by
  have hh := mul_le_mul_of_nonneg_left P.retained (by norm_num : (0:ℝ)≤3/4)
  have hh' : ((3/4:ℝ)*AngularSeedPieces.retentionRate k P.J)*(∑ i,volume.real (Y i)) ≤
      ∑ g ∈ P.groups, (3/4:ℝ)*MeasurableAngularPruning.mass volume (P.shading g) := by
    calc
      _ ≤ (3/4:ℝ)*(∑ g ∈ P.groups, MeasurableAngularPruning.mass volume (P.shading g)) := by
        simpa only [mul_assoc] using hh
      _ = _ := Finset.mul_sum _ _ _
  apply hh'.trans
  apply Finset.sum_le_sum
  intro g hg
  have hs := SpatialMarkedPartition.marked_mass volume (angularShading P g) (label P g)
    (Nat.cast_pos.mpr (SpatialTubeCover.overlapConstant_pos k
      (2+coverWidth width upperLength) ((k:ℝ)+coverWidth width upperLength+3)))
    (MeasurableAngularGroups.compressed_measurable _ _ (P.measurable g))
    (MeasurableAngularGroups.compressed_finite volume _ _ (P.finite g))
    (fun x => Nat.cast_le.mpr (occupied_labels P length g hg hδ hδ1 hw hL hcarrier x))
  rw [angularShading,MeasurableAngularGroups.mass_eq] at hs
  exact hs

theorem spatial_overlap (P : MeasurableAngularPieces.Pieces F Y δ beta)
    (length : Fin M → ℝ) (g : Fin M) (hg : g ∈ P.groups)
    (hδ : 0 < δ) (hδ1 : δ ≤ 1) (hw : 0 ≤ width)
    (hL : ∀ i, length i ≤ upperLength)
    (hcarrier : ∀ i, Y i ⊆ SamplingGeometry.lengthCarrier (F.tube i) (length i) (width*δ))
    (x : Space (k+1)) :
    (occupied P (coverWidth width upperLength) g x).card ≤
      spatialConstant k (coverWidth width upperLength) := by
  have hs : occupied P (coverWidth width upperLength) g x ⊆
      (Finset.univ.filter (fun i => x ∈ angularShading P g i)).image (label P g) := by
    intro q hq
    obtain ⟨i,hi⟩ := (Finset.mem_filter.mp hq).2
    refine Finset.mem_image.mpr ⟨MeasurableMarkedSelection.index
      (SpatialMarkedPartition.indices (label P g) q) i,Finset.mem_filter.mpr ⟨Finset.mem_univ _,hi.1⟩,?_⟩
    exact SpatialMarkedPartition.index_label (label P g) q i
  exact (Finset.card_le_card hs).trans (occupied_labels P length g hg hδ hδ1 hw hL hcarrier x)

theorem total_overlap (P : MeasurableAngularPieces.Pieces F Y δ beta)
    (length : Fin M → ℝ) (hδ : 0 < δ) (hδ1 : δ ≤ 1) (hw : 0 ≤ width)
    (hL : ∀ i, length i ≤ upperLength)
    (hcarrier : ∀ i, Y i ⊆ SamplingGeometry.lengthCarrier (F.tube i) (length i) (width*δ))
    (x : Space (k+1)) :
    (∑ g ∈ P.groups, ((occupied P (coverWidth width upperLength) g x).card:ℝ)) ≤
      (2*(spatialConstant k (coverWidth width upperLength):ℝ))*P.tau^(-beta) := by
  let A := P.groups.filter (fun g => ∃ i,x ∈ P.shading g i)
  have he : (∑ g ∈ P.groups, ((occupied P (coverWidth width upperLength) g x).card:ℝ)) =
      ∑ g ∈ A, ((occupied P (coverWidth width upperLength) g x).card:ℝ) := by
    symm
    apply Finset.sum_subset (Finset.filter_subset _ _)
    intro g hg hga
    have hn : ¬∃ i,x ∈ P.shading g i := by simpa only [A,Finset.mem_filter,hg,true_and] using hga
    have hz : occupied P (coverWidth width upperLength) g x = ∅ := by
      apply Finset.eq_empty_iff_forall_notMem.mpr
      intro q hq
      obtain ⟨i,hi⟩ := (Finset.mem_filter.mp hq).2
      exact hn ⟨_,shading_subset_angular P _ g q i hi⟩
    simp only [hz,Finset.card_empty,Nat.cast_zero]
  rw [he]
  have hs : (∑ g ∈ A, ((occupied P (coverWidth width upperLength) g x).card:ℝ)) ≤
      ∑ _g ∈ A, (spatialConstant k (coverWidth width upperLength):ℝ) :=
    Finset.sum_le_sum (fun g hg => Nat.cast_le.mpr
      (spatial_overlap P length g (Finset.mem_filter.mp hg).1 hδ hδ1 hw hL hcarrier x))
  simp only [Finset.sum_const,nsmul_eq_mul] at hs
  have hh := mul_le_mul_of_nonneg_right (P.overlap x)
    (Nat.cast_nonneg (spatialConstant k (coverWidth width upperLength)))
  exact hs.trans (by simpa only [A,mul_assoc,mul_comm,mul_left_comm] using hh)

/-- All indices, sets and families remain the literal definitions from the
unit-axis spatial decomposition, with the fixed cover coefficient enlarged.
The containing-carrier field explicitly uses each original axis length. -/
structure Decomposition (F : TubeFamily (k+1) M) (Y : Fin M → Set (Space (k+1)))
    (length : Fin M → ℝ) (δ beta width upperLength : ℝ) where
  angular : MeasurableAngularPieces.Pieces F Y δ beta
  retained : MeasurableAngularDecomposition.retentionConstant k*(Real.log (2/δ))^(-(3:ℝ))*(∑ i,volume.real (Y i)) ≤
    ∑ g ∈ angular.groups, ∑ q ∈ labels angular g, ∑ i,
      volume.real (shading angular (coverWidth width upperLength) g q i)
  overlap : ∀ x, (∑ g ∈ angular.groups, ((occupied angular (coverWidth width upperLength) g x).card:ℝ)) ≤
    (2*(spatialConstant k (coverWidth width upperLength):ℝ))*angular.tau^(-beta)
  broad : ∀ g ∈ angular.groups, ∀ q x,
    Broad (family angular g q)
      (Finset.univ.filter (fun i => x ∈ shading angular (coverWidth width upperLength) g q i))
      δ beta angular.tau (64*AngularSeedPieces.angularConstant k*spatialConstant k (coverWidth width upperLength))
  containing_box : ∀ g ∈ angular.groups, ∀ q i,
    SamplingGeometry.lengthCarrier ((family angular g q).tube i)
      (length (originalIndex angular g q i)) (width*δ) ⊆
      SpatialTubeCover.parallelBox (F.tube g).direction angular.tau q
        (2+coverWidth width upperLength) ((k:ℝ)+coverWidth width upperLength+3)
  containing_tube : ∀ g ∈ angular.groups, ∀ q i,
    SamplingGeometry.lengthCarrier ((family angular g q).tube i)
      (length (originalIndex angular g q i)) (width*δ) ⊆
      SamplingGeometry.lengthCarrier
        (SpatialTubeCover.containingTube (F.tube g).direction (F.tube g).unit_direction
          angular.tau q (2+coverWidth width upperLength)) (2*(2+coverWidth width upperLength))
            (((k:ℝ)+coverWidth width upperLength+3)*angular.tau)

/-- Measurable Lemma 3.2 with actual variable finite axes, arbitrary positions,
fixed width and any fixed upper length. Every positive comparable length range
in the manuscript is included; no lower length is required by the proof. -/
theorem construct (F : TubeFamily (k+1) M) (Y : Fin M → Set (Space (k+1)))
    (length : Fin M → ℝ) (hδ : 0 < δ) (hδ1 : δ ≤ 1) (hb : 0 ≤ beta) (hb1 : beta ≤ 1)
    (hw : 0 ≤ width) (hL : ∀ i,length i ≤ upperLength)
    (hY : ∀ i,MeasurableSet (Y i))
    (hcarrier : ∀ i,Y i ⊆ SamplingGeometry.lengthCarrier (F.tube i) (length i) (width*δ)) :
    Nonempty (Decomposition F Y length δ beta width upperLength) := by
  have hf (i) : volume (Y i) ≠ ∞ :=
    measure_ne_top_of_subset (hcarrier i) (MeasurableSeedLengths.lengthCarrier_finite _ _ _)
  obtain ⟨P⟩ := MeasurableAngularDecomposition.exists_angular_pieces F Y hδ hδ1 hb hY hf
  refine ⟨⟨P,?_,total_overlap P length hδ hδ1 hw hL hcarrier,?_,
    fun g hg q i => containing_box P length g hg q i hδ hδ1 hw hL,
    fun g hg q i => containing_tube P length g hg q i hδ hδ1 hw hL⟩⟩
  · exact (mul_le_mul_of_nonneg_right (MeasurableAngularDecomposition.cubic_log_rate k P.J hδ hδ1 P.depth)
      (Finset.sum_nonneg (fun _ _ => measureReal_nonneg))).trans
        (retained_mass P length hδ hδ1 hw hL hcarrier)
  · intro g hg q x center r hr
    have hh := MeasurableAngularSpatial.broad P (width:=coverWidth width upperLength) hδ g hg q x center r hr
    have hp : (4:ℝ)^beta ≤ 4 := by
      simpa using Real.rpow_le_rpow_of_exponent_le (by norm_num : (1:ℝ)≤4) hb1
    have hcoeff : (4:ℝ)^beta*(4*AngularSeedPieces.angularConstant k)*(4*spatialConstant k (coverWidth width upperLength)) ≤
        64*AngularSeedPieces.angularConstant k*spatialConstant k (coverWidth width upperLength) := by
      nlinarith [AngularSeedPieces.angularConstant_pos k,
        mul_le_mul_of_nonneg_right hp (show 0 ≤ 16*AngularSeedPieces.angularConstant k*spatialConstant k (coverWidth width upperLength)
          by positivity [AngularSeedPieces.angularConstant_pos k])]
    exact hh.trans (mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_right hcoeff (Real.rpow_nonneg
        (div_nonneg (hδ.le.trans hr) (hδ.trans_le P.lower_scale).le) beta)) (Nat.cast_nonneg _))

end
end KakeyaFormal.MeasurableAngularSpatialLengths
