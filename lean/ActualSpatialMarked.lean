import SpatialMarkedPartition

/-! Actual spatial labels and common parallel boxes for measurable angular
pieces. Overlap and marked retention follow from the original physical tube
geometry; no common-box or bounded-label-count premise is supplied. -/
namespace KakeyaFormal.ActualSpatialMarked
open Finset MeasureTheory SpatialAngular SpatialMarkedPartition AngularDecomposition MeasurableEnergy
open scoped BigOperators ENNReal
noncomputable section
open Classical

def overlapConstant (k : ℕ) (width angular : ℝ) : ℕ :=
  (2*Nat.ceil (((k:ℝ)+width+angular)/2)+3)^k

def label {k M : ℕ} (F : TubeFamily (k+1) M) (u : Space (k+1)) (tau : ℝ) : Fin M → Cell k :=
  fun i => spatialLabel u tau (F.tube i)

theorem overlapConstant_pos (k : ℕ) (width angular : ℝ) : 0 < overlapConstant k width angular := by
  unfold overlapConstant
  positivity

/-- Actual tube incidence implies a dimension-only occupied-label bound. -/
theorem occupied_labels {k M : ℕ} (F : TubeFamily (k+1) M) (u : Space (k+1))
    (Y : Fin M → Set (Space (k+1))) {δ tau width angular : ℝ}
    (hu : ‖u‖=1) (htau : 0 < tau) (hδtau : δ ≤ tau)
    (hw : 0 ≤ width) (ha : 0 ≤ angular)
    (hlocal : ∀ i, projectiveDistance (F.tube i).direction u ≤ angular*tau)
    (hcarrier : ∀ i, Y i ⊆ (F.tube i).carrier (width*δ)) (x : Space (k+1)) :
    ((univ.filter (fun i => x ∈ Y i)).image (label F u tau)).card ≤ overlapConstant k width angular :=
  occupied_spatial_labels u hu F.tube _ x htau hδtau hw ha
    (fun i _ => hlocal i) (fun i hi => hcarrier i (mem_filter.mp hi).2)

/-- Every tube in each label fiber is contained in the SAME actual parallel
box. This follows from the original base quantization, not a box hypothesis. -/
theorem common_box {k M : ℕ} (F : TubeFamily (k+1) M) (u : Space (k+1))
    {δ tau width angular R : ℝ}
    (hu : ‖u‖=1) (htau : 0 < tau) (hδtau : δ ≤ tau) (hδ1 : δ ≤ 1)
    (hw : 0 ≤ width) (ha : 0 ≤ angular) (hbounded : F.Bounded R)
    (hlocal : ∀ i, projectiveDistance (F.tube i).direction u ≤ angular*tau)
    (q : Cell k) (i : Fin (indices (label F u tau) q).card) :
    ((SpatialMarkedPartition.family F (label F u tau) q).tube i).carrier (width*δ) ⊆
      parallelBox u tau q (R+1+width) ((k:ℝ)+width+angular) := by
  have hh := bounded_tube_spatial_box u hu (F.tube (MeasurableMarkedSelection.index _ i))
    htau hδtau hδ1 hw ha (hbounded _) (hlocal _)
  have heq := index_label (label F u tau) q i
  change spatialLabel u tau (F.tube (MeasurableMarkedSelection.index _ i))=q at heq
  rwa [heq] at hh

/-- In particular the original base of every reindexed tube is in that box,
which is the literal geometric input to the joint normalization adapter. -/
theorem common_base_box {k M : ℕ} (F : TubeFamily (k+1) M) (u : Space (k+1))
    {δ tau width angular R : ℝ}
    (hu : ‖u‖=1) (hδ : 0 < δ) (htau : 0 < tau) (hδtau : δ ≤ tau) (hδ1 : δ ≤ 1)
    (hw : 0 ≤ width) (ha : 0 ≤ angular) (hbounded : F.Bounded R)
    (hlocal : ∀ i, projectiveDistance (F.tube i).direction u ≤ angular*tau)
    (q : Cell k) (i : Fin (indices (label F u tau) q).card) :
    ((SpatialMarkedPartition.family F (label F u tau) q).tube i).base ∈
      parallelBox u tau q (R+1+width) ((k:ℝ)+width+angular) := by
  apply common_box F u hu htau hδtau hδ1 hw ha hbounded hlocal q i
  exact ⟨0,⟨by norm_num,by norm_num⟩,by simp [UnitTube.axisPoint,mul_nonneg hw hδ.le]⟩

/-- Whole full shadings inherit all original tube geometry after injective
spatial reindexing; no population factor is spent on one preferred box. -/
theorem family_geometry {k M : ℕ} (F : TubeFamily (k+1) M) (u : Space (k+1))
    {tau δ m A angular : ℝ}
    (hsep : F.Separated δ) (hcap : F.CapBound δ m A)
    (hlocal : ∀ i, projectiveDistance (F.tube i).direction u ≤ angular*tau) (q : Cell k) :
    (SpatialMarkedPartition.family F (label F u tau) q).Separated δ ∧
    (SpatialMarkedPartition.family F (label F u tau) q).CapBound δ m A ∧
    ∀ i, projectiveDistance ((SpatialMarkedPartition.family F (label F u tau) q).tube i).direction u ≤ angular*tau :=
  ⟨MeasurableMarkedSelection.family_separated F _ hsep,
   MeasurableMarkedSelection.family_cap_bound F _ hcap,fun _ => hlocal _⟩

/-- All actual spatial labels retain three quarters of original marked mass,
with the bounded overlap derived from tube carriers and the angular cap. -/
theorem marked_mass {k M : ℕ} (F : TubeFamily (k+1) M) (u : Space (k+1))
    (Y G : Fin M → Set (Space (k+1))) {δ tau width angular : ℝ}
    (hu : ‖u‖=1) (htau : 0 < tau) (hδtau : δ ≤ tau)
    (hw : 0 ≤ width) (ha : 0 ≤ angular)
    (hlocal : ∀ i, projectiveDistance (F.tube i).direction u ≤ angular*tau)
    (hcarrier : ∀ i, Y i ⊆ (F.tube i).carrier (width*δ)) (hsub : ∀ i, G i ⊆ Y i)
    (hG : ∀ i, MeasurableSet (G i)) :
    (3/4:ℝ)*(∑ i, (volume : Measure (Space (k+1))).real (G i)) ≤
      ∑ q ∈ labels (label F u tau), ∑ i,
        (volume : Measure (Space (k+1))).real (Marks G (label F u tau) (overlapConstant k width angular:ℝ) q i) := by
  apply SpatialMarkedPartition.marked_mass volume G (label F u tau)
    (Nat.cast_pos.mpr (overlapConstant_pos k width angular)) hG
    (fun i => measure_ne_top_of_subset ((hsub i).trans (hcarrier i)) (TubeVolume.carrier_finite _ _))
  intro x
  exact_mod_cast occupied_labels F u G hu htau hδtau hw ha hlocal (fun i => (hsub i).trans (hcarrier i)) x

/-- The whole full unions of the spatial subpieces have fixed pointwise
summed overlap in the ORIGINAL physical coordinates. -/
theorem full_overlap {k M : ℕ} (F : TubeFamily (k+1) M) (u : Space (k+1))
    (Y : Fin M → Set (Space (k+1))) {δ tau width angular : ℝ}
    (hu : ‖u‖=1) (htau : 0 < tau) (hδtau : δ ≤ tau)
    (hw : 0 ≤ width) (ha : 0 ≤ angular)
    (hlocal : ∀ i, projectiveDistance (F.tube i).direction u ≤ angular*tau)
    (hcarrier : ∀ i, Y i ⊆ (F.tube i).carrier (width*δ)) (x : Space (k+1)) :
    overlapCount (fun q : ↥(labels (label F u tau)) => ⋃ i, Full Y (label F u tau) q.val i) x ≤
      overlapConstant k width angular :=
  (SpatialMarkedPartition.full_overlap Y (label F u tau) x).trans
    (occupied_labels F u Y hu htau hδtau hw ha hlocal hcarrier x)

/-- The same bounded overlap controls the SUM of full-subpiece volumes. -/
theorem full_union_volume {k M : ℕ} (F : TubeFamily (k+1) M) (u : Space (k+1))
    (Y : Fin M → Set (Space (k+1))) {δ tau width angular : ℝ}
    (hu : ‖u‖=1) (htau : 0 < tau) (hδtau : δ ≤ tau)
    (hw : 0 ≤ width) (ha : 0 ≤ angular)
    (hlocal : ∀ i, projectiveDistance (F.tube i).direction u ≤ angular*tau)
    (hcarrier : ∀ i, Y i ⊆ (F.tube i).carrier (width*δ)) (hY : ∀ i, MeasurableSet (Y i)) :
    (∑ q : ↥(labels (label F u tau)), (volume : Measure (Space (k+1))).real
      (⋃ i, Full Y (label F u tau) q.val i)) ≤
      (overlapConstant k width angular:ℝ)*(volume : Measure (Space (k+1))).real (⋃ i, Y i) := by
  apply SpatialMarkedPartition.full_union_volume volume Y (label F u tau) hY
    (fun i => measure_ne_top_of_subset (hcarrier i) (TubeVolume.carrier_finite _ _))
  intro x
  exact_mod_cast occupied_labels F u Y hu htau hδtau hw ha hlocal hcarrier x

end
end KakeyaFormal.ActualSpatialMarked
