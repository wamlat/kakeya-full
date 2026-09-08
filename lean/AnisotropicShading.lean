import AnisotropicVolume
import AnisotropicCap
import TubeVolume

/-! One actual unit segment is selected per original tube by maximal measurable
shading mass. This preserves the common anisotropic union comparison and does
not create repeated parallel directions. -/
namespace KakeyaFormal.AnisotropicShading
open EuclideanSplit SpatialAngular AnisotropicRescaling AnisotropicVolume TubeVolume MeasureTheory
open scoped ENNReal BigOperators
noncomputable section
open Classical

/-- The fixed number of unit segments in the actual transformed carrier cover. -/
def segmentCount (angular : ℝ) : ℕ := Nat.ceil (1+angular)+1

theorem segmentCount_pos (angular : ℝ) : 0 < segmentCount angular := Nat.succ_pos _

/-- Actual measurable candidate: intersect the exact affine image with one
of the explicit unit carriers. No rounded-cell enlargement is made. -/
def segmentSet {k : ℕ} (u : Space (k+1)) {tau : ℝ} (htau : tau ≠ 0)
    (q : Cell k) (T : UnitTube (k+1)) (width δ : ℝ) (Y : Set (Space (k+1))) (j : ℕ) :
    Set (Space (k+1)) :=
  (normalizeBox u tau q '' Y) ∩ (transformedTube u htau q T j).carrier (width*(δ/tau))

theorem segmentSet_measurable {k : ℕ} (u : Space (k+1)) {tau : ℝ} (htau : tau ≠ 0)
    (q : Cell k) (T : UnitTube (k+1)) (width δ : ℝ)
    {Y : Set (Space (k+1))} (hY : MeasurableSet Y) (j : ℕ) :
    MeasurableSet (segmentSet u htau q T width δ Y j) :=
  (normalizeBox_image_measurable u htau q hY).inter (carrier_measurable _ _)

theorem segmentSet_finite {k : ℕ} (u : Space (k+1)) {tau : ℝ} (htau : tau ≠ 0)
    (q : Cell k) (T : UnitTube (k+1)) (width δ : ℝ) (Y : Set (Space (k+1))) (j : ℕ) :
    volume (segmentSet u htau q T width δ Y j) ≠ ∞ :=
  measure_ne_top_of_subset Set.inter_subset_right (carrier_finite _ _)

/-- The exact transformed shading is covered by these actual candidate subsets. -/
theorem segmentSet_union {k : ℕ} (u : Space (k+1)) {tau angular width δ : ℝ}
    (hu : ‖u‖ = 1) (htau : 0 < tau) (htau1 : tau ≤ 1)
    (q : Cell k) (T : UnitTube (k+1)) (Y : Set (Space (k+1)))
    (hcap : projectiveDistance T.direction u ≤ angular*tau) (hYT : Y ⊆ T.carrier (width*δ)) :
    (⋃ j ∈ Finset.range (segmentCount angular), segmentSet u htau.ne' q T width δ Y j) =
      normalizeBox u tau q '' Y := by
  ext x
  constructor
  · intro hx
    obtain ⟨j,_hj,hxj⟩ := Set.mem_iUnion₂.mp hx
    exact hxj.1
  · rintro ⟨y,hy,rfl⟩
    obtain ⟨j,hj,hjcarrier⟩ := transformed_carrier_unit_cover u q T hu htau htau1 hcap (hYT hy)
    exact Set.mem_iUnion₂.mpr ⟨j,hj,⟨⟨y,hy,rfl⟩,hjcarrier⟩⟩

/-- Candidate masses dominate the exact image mass by finite subadditivity. -/
theorem segment_mass_cover {k : ℕ} (u : Space (k+1)) {tau angular width δ : ℝ}
    (hu : ‖u‖ = 1) (htau : 0 < tau) (htau1 : tau ≤ 1)
    (q : Cell k) (T : UnitTube (k+1)) (Y : Set (Space (k+1)))
    (hcap : projectiveDistance T.direction u ≤ angular*tau) (hYT : Y ⊆ T.carrier (width*δ)) :
    (volume : Measure (Space (k+1))).real Y/tau^k ≤
      ∑ j ∈ Finset.range (segmentCount angular),
        (volume : Measure (Space (k+1))).real (segmentSet u htau.ne' q T width δ Y j) := by
  have h := measureReal_biUnion_finset_le (μ := (volume : Measure (Space (k+1))))
    (Finset.range (segmentCount angular)) (segmentSet u htau.ne' q T width δ Y)
  rw [segmentSet_union u hu htau htau1 q T Y hcap hYT,normalizeBox_realVolume u htau] at h
  exact h

/-- A finite maximum chooses exactly one unit segment per original tube. -/
def bestSegment {k : ℕ} (u : Space (k+1)) {tau : ℝ} (htau : tau ≠ 0)
    (q : Cell k) (T : UnitTube (k+1)) (angular width δ : ℝ) (Y : Set (Space (k+1))) : ℕ :=
  (Finset.exists_max_image (Finset.range (segmentCount angular))
    (fun j => (volume : Measure (Space (k+1))).real (segmentSet u htau q T width δ Y j))
    (Finset.nonempty_range_iff.mpr (segmentCount_pos angular).ne')).choose

theorem bestSegment_spec {k : ℕ} (u : Space (k+1)) {tau : ℝ} (htau : tau ≠ 0)
    (q : Cell k) (T : UnitTube (k+1)) (angular width δ : ℝ) (Y : Set (Space (k+1))) :
    bestSegment u htau q T angular width δ Y ∈ Finset.range (segmentCount angular) ∧
      ∀ j ∈ Finset.range (segmentCount angular),
        (volume : Measure (Space (k+1))).real (segmentSet u htau q T width δ Y j) ≤
          (volume : Measure (Space (k+1))).real (segmentSet u htau q T width δ Y
            (bestSegment u htau q T angular width δ Y)) :=
  (Finset.exists_max_image (Finset.range (segmentCount angular))
    (fun j => (volume : Measure (Space (k+1))).real (segmentSet u htau q T width δ Y j))
    (Finset.nonempty_range_iff.mpr (segmentCount_pos angular).ne')).choose_spec

/-- The actual chosen measurable shading. -/
def selectedSet {k : ℕ} (u : Space (k+1)) {tau : ℝ} (htau : tau ≠ 0)
    (q : Cell k) (T : UnitTube (k+1)) (angular width δ : ℝ) (Y : Set (Space (k+1))) :
    Set (Space (k+1)) :=
  segmentSet u htau q T width δ Y (bestSegment u htau q T angular width δ Y)

/-- Every original tube retains the stated fixed fraction of its exact image
mass, irrespective of other tubes or overlap patterns. -/
theorem selected_mass_lower {k : ℕ} (u : Space (k+1)) {tau angular width δ : ℝ}
    (hu : ‖u‖ = 1) (htau : 0 < tau) (htau1 : tau ≤ 1)
    (q : Cell k) (T : UnitTube (k+1)) (Y : Set (Space (k+1)))
    (hcap : projectiveDistance T.direction u ≤ angular*tau) (hYT : Y ⊆ T.carrier (width*δ)) :
    (volume : Measure (Space (k+1))).real Y/(tau^k*(segmentCount angular:ℝ)) ≤
      (volume : Measure (Space (k+1))).real (selectedSet u htau.ne' q T angular width δ Y) := by
  have hcover := segment_mass_cover u hu htau htau1 q T Y hcap hYT
  have hmax := (bestSegment_spec u htau.ne' q T angular width δ Y).2
  have hsum := Finset.sum_le_sum (s := Finset.range (segmentCount angular)) hmax
  simp only [Finset.sum_const,Finset.card_range,nsmul_eq_mul] at hsum
  have hN : (0:ℝ) < segmentCount angular := Nat.cast_pos.mpr (segmentCount_pos angular)
  have h : ((volume : Measure (Space (k+1))).real Y/tau^k)/(segmentCount angular:ℝ) ≤
      (volume : Measure (Space (k+1))).real (selectedSet u htau.ne' q T angular width δ Y) :=
    (div_le_iff₀ hN).mpr (by
      simpa only [mul_comm,selectedSet] using hcover.trans hsum)
  simpa only [div_div] using h

/-- The upper mass comparison and carrier containment are literal set inclusions. -/
theorem selected_subset {k : ℕ} (u : Space (k+1)) {tau : ℝ} (htau : tau ≠ 0)
    (q : Cell k) (T : UnitTube (k+1)) (angular width δ : ℝ) (Y : Set (Space (k+1))) :
    selectedSet u htau q T angular width δ Y ⊆ normalizeBox u tau q '' Y ∧
      selectedSet u htau q T angular width δ Y ⊆
        (transformedTube u htau q T (bestSegment u htau q T angular width δ Y)).carrier
          (width*(δ/tau)) := ⟨Set.inter_subset_left,Set.inter_subset_right⟩

theorem selected_measurable {k : ℕ} (u : Space (k+1)) {tau : ℝ} (htau : tau ≠ 0)
    (q : Cell k) (T : UnitTube (k+1)) (angular width δ : ℝ)
    {Y : Set (Space (k+1))} (hY : MeasurableSet Y) :
    MeasurableSet (selectedSet u htau q T angular width δ Y) :=
  segmentSet_measurable u htau q T width δ hY _

theorem selected_finite {k : ℕ} (u : Space (k+1)) {tau : ℝ} (htau : tau ≠ 0)
    (q : Cell k) (T : UnitTube (k+1)) (angular width δ : ℝ) (Y : Set (Space (k+1))) :
    volume (selectedSet u htau q T angular width δ Y) ≠ ∞ :=
  segmentSet_finite u htau q T width δ Y _

/-- All independently chosen unit segments remain inside the one common
anisotropic image union. There is no cell-thickening factor. -/
theorem selected_union_subset {k : ℕ} {I : Type*} (u : Space (k+1)) {tau : ℝ}
    (htau : tau ≠ 0) (q : Cell k) (T : I → UnitTube (k+1))
    (angular width δ : ℝ) (Y : I → Set (Space (k+1))) :
    (⋃ i, selectedSet u htau q (T i) angular width δ (Y i)) ⊆
      normalizeBox u tau q '' (⋃ i, Y i) := by
  intro x hx
  obtain ⟨i,hi⟩ := Set.mem_iUnion.mp hx
  obtain ⟨y,hy,rfl⟩ := (selected_subset u htau q (T i) angular width δ (Y i)).1 hi
  exact ⟨y,Set.mem_iUnion.mpr ⟨i,hy⟩,rfl⟩

/-- Exact global volume comparison for a finite original family. -/
theorem selected_union_volume {k : ℕ} {I : Type*} [Fintype I] (u : Space (k+1)) {tau : ℝ}
    (htau : 0 < tau) (q : Cell k) (T : I → UnitTube (k+1))
    (angular width δ : ℝ) (Y : I → Set (Space (k+1))) (hY : ∀ i, volume (Y i) ≠ ∞) :
    (volume : Measure (Space (k+1))).real (⋃ i, selectedSet u htau.ne' q (T i) angular width δ (Y i)) ≤
      (volume : Measure (Space (k+1))).real (⋃ i, Y i)/tau^k := by
  have hU : volume (⋃ i, Y i) ≠ ∞ := by
    simpa only [Set.biUnion_univ] using measure_biUnion_ne_top (μ := (volume : Measure (Space (k+1))))
      (s := Set.univ) (f := Y) (Set.toFinite _) (fun i _ => hY i)
  have h := measureReal_mono (selected_union_subset u htau.ne' q T angular width δ Y)
    (normalizeBox_volume_finite u htau q hU)
  rwa [normalizeBox_realVolume u htau] at h

end
end KakeyaFormal.AnisotropicShading
