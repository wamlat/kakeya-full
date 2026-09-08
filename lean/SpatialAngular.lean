import AngularAssignment
import GridCells
import EuclideanSplit

/-! Actual parallel spatial covers for one angular cap. Axes are an explicit
transverse integer lattice in an actual orthogonal frame. -/
namespace KakeyaFormal.SpatialAngular
open KakeyaFormal.EuclideanSplit
noncomputable section

/-- The transverse coordinate in the orthogonal frame aligned with u. -/
def transverse {k : ℕ} (u x : Space (k+1)) : Space k := tail (alignStem u x)

theorem transverse_sub {k : ℕ} (u x y : Space (k+1)) :
    transverse u (x-y) = transverse u x-transverse u y := by simp [transverse]

theorem transverse_add {k : ℕ} (u x y : Space (k+1)) :
    transverse u (x+y) = transverse u x+transverse u y := by simp [transverse]

theorem transverse_smul {k : ℕ} (u x : Space (k+1)) (t : ℝ) :
    transverse u (t • x) = t • transverse u x := by simp [transverse]

theorem transverse_norm_le {k : ℕ} (u x : Space (k+1)) : ‖transverse u x‖ ≤ ‖x‖ :=
  (tail_norm_le _).trans (le_of_eq ((alignStem u).norm_map x))

theorem transverse_axis_zero {k : ℕ} (u : Space (k+1)) (hu : ‖u‖ = 1) :
    transverse u u = 0 := by simp [transverse,alignStem_apply u hu,axisUnit]

/-- The unoriented angular chord controls the actual transverse direction size. -/
theorem transverse_direction_le {k : ℕ} (u v : Space (k+1)) (hu : ‖u‖ = 1) :
    ‖transverse u v‖ ≤ projectiveDistance v u := by
  apply le_min
  · have h := transverse_norm_le u (v-u)
    simpa only [transverse_sub,transverse_axis_zero u hu,sub_zero] using h
  · have h := transverse_norm_le u (v+u)
    simpa only [transverse_add,transverse_axis_zero u hu,add_zero] using h

/-- Explicit transverse lattice label of an original tube's base. -/
def spatialLabel {k : ℕ} (u : Space (k+1)) (tau : ℝ) (T : UnitTube (k+1)) : Cell k :=
  GridCells.label (2*tau) (transverse u T.base)

/-- A parallel cylinder about the explicit transverse lattice axis. -/
def cylinder {k : ℕ} (u : Space (k+1)) (tau : ℝ) (q : Cell k) (W : ℝ) : Set (Space (k+1)) :=
  {x | dist (transverse u x) (cellCenter (2*tau) q) ≤ W*tau}

/-- Every actual tube in the cap is contained in its one assigned parallel
cylinder, including its full endpoint caps. -/
theorem tube_in_spatial_cylinder {k : ℕ} (u : Space (k+1)) (hu : ‖u‖ = 1)
    (T : UnitTube (k+1)) {δ tau width angular : ℝ}
    (htau : 0 < tau) (hdr : δ ≤ tau) (hw : 0 ≤ width) (ha : 0 ≤ angular)
    (hcap : projectiveDistance T.direction u ≤ angular*tau) :
    T.carrier (width*δ) ⊆ cylinder u tau (spatialLabel u tau T) ((k:ℝ)+width+angular) := by
  intro x hx
  obtain ⟨t,ht,hxt⟩ := hx
  have htpos : 0 ≤ t := ht.1
  have hterr : ‖transverse u (x-T.axisPoint t)‖ ≤ width*δ :=
    (transverse_norm_le _ _).trans hxt
  have htdir : ‖transverse u T.direction‖ ≤ angular*tau := (transverse_direction_le u _ hu).trans hcap
  have hscalar : ‖t • transverse u T.direction‖ ≤ angular*tau := by
    rw [norm_smul,Real.norm_eq_abs,abs_of_nonneg htpos]
    have h1 := mul_le_mul_of_nonneg_left htdir htpos
    exact h1.trans (by simpa only [one_mul] using
      mul_le_mul_of_nonneg_right ht.2 (mul_nonneg ha htau.le))
  have heq : transverse u x-transverse u T.base =
      transverse u (x-T.axisPoint t)+t • transverse u T.direction := by
    rw [transverse_sub,UnitTube.axisPoint,transverse_add,transverse_smul]
    abel
  have hnear : dist (transverse u x) (transverse u T.base) ≤ (width+angular)*tau := by
    rw [dist_eq_norm,heq]
    have h := norm_add_le (transverse u (x-T.axisPoint t)) (t • transverse u T.direction)
    nlinarith [mul_le_mul_of_nonneg_left hdr hw]
  have hquant := GridCells.cell_center_distance (GridCells.gridCell_covers
    (by positivity : 0 < 2*tau) (transverse u T.base))
  have htri := dist_triangle (transverse u x) (transverse u T.base)
    (cellCenter (2*tau) (spatialLabel u tau T))
  change dist (transverse u x) (cellCenter (2*tau) (spatialLabel u tau T)) ≤ ((k:ℝ)+width+angular)*tau
  change dist (transverse u T.base) (cellCenter (2*tau) (spatialLabel u tau T)) ≤ (k:ℝ)*(2*tau)/2 at hquant
  linarith

/-- Actual pointwise overlap of distinct parallel cylinders is bounded solely
by dimension and width, by counting their explicit transverse lattice centers. -/
theorem cylinder_overlap {k : ℕ} (u x : Space (k+1)) {tau W : ℝ}
    (htau : 0 < tau) (labels : Finset (Cell k))
    (hpoint : ∀ q ∈ labels, x ∈ cylinder u tau q W) :
    labels.card ≤ (2*Nat.ceil (W/2)+3)^k := by
  apply GridGeometry.ball_grid_count (by positivity : 0 < 2*tau) (transverse u x) labels
  intro q hq
  have hp := hpoint q hq
  change dist (cellCenter (2*tau) q) (transverse u x) ≤ (W/2)*(2*tau)
  change dist (transverse u x) (cellCenter (2*tau) q) ≤ W*tau at hp
  have heq : (W/2)*(2*tau) = W*tau := by ring
  simpa only [dist_comm,heq] using hp

/-- Distinct labels of tubes meeting a point in the same angular cap obey the
same genuine dimensional spatial-overlap bound. -/
theorem occupied_spatial_labels {ι : Type*} {k : ℕ} (u : Space (k+1)) (hu : ‖u‖ = 1)
    (tubes : ι → UnitTube (k+1)) (indices : Finset ι) (x : Space (k+1))
    {δ tau width angular : ℝ} (htau : 0 < tau) (hdr : δ ≤ tau)
    (hw : 0 ≤ width) (ha : 0 ≤ angular)
    (hcap : ∀ i ∈ indices, projectiveDistance (tubes i).direction u ≤ angular*tau)
    (hpoint : ∀ i ∈ indices, x ∈ (tubes i).carrier (width*δ)) :
    (indices.image (fun i => spatialLabel u tau (tubes i))).card ≤
      (2*Nat.ceil (((k:ℝ)+width+angular)/2)+3)^k := by
  classical
  apply cylinder_overlap u x htau
  intro q hq
  obtain ⟨i,hi,rfl⟩ := Finset.mem_image.mp hq
  exact tube_in_spatial_cylinder u hu (tubes i) htau hdr hw ha (hcap i hi) (hpoint i hi)

/-- A genuine finite-length parallel spatial box in the aligned frame. -/
def parallelBox {k : ℕ} (u : Space (k+1)) (tau : ℝ) (q : Cell k)
    (longitudinal W : ℝ) : Set (Space (k+1)) :=
  {x | |head (alignStem u x)| ≤ longitudinal ∧ x ∈ cylinder u tau q W}

/-- The actual point on the lattice axis at longitudinal coordinate s. -/
def latticeAxisPoint {k : ℕ} (u : Space (k+1)) (tau : ℝ) (q : Cell k) (s : ℝ) : Space (k+1) :=
  (alignStem u).symm (cons s (cellCenter (2*tau) q))

/-- Distance to the matching lattice-axis point is exactly transverse distance. -/
theorem matching_axis_distance {k : ℕ} (u x : Space (k+1)) (tau : ℝ) (q : Cell k) :
    dist x (latticeAxisPoint u tau q (head (alignStem u x))) =
      dist (transverse u x) (cellCenter (2*tau) q) := by
  rw [dist_eq_norm,← (alignStem u).norm_map]
  have heq : alignStem u (x-latticeAxisPoint u tau q (head (alignStem u x))) =
      cons 0 (transverse u x-cellCenter (2*tau) q) := by
    rw [map_sub,latticeAxisPoint,(alignStem u).apply_symm_apply]
    ext i
    cases i using Fin.cases <;> simp [cons,head,tail,transverse]
  rw [heq,norm_cons_zero,dist_eq_norm]

/-- A box is contained in the specified thickness of a finite lattice-axis segment. -/
theorem parallelBox_axis_segment {k : ℕ} (u : Space (k+1)) (tau : ℝ) (q : Cell k)
    (R W : ℝ) {x : Space (k+1)} (hx : x ∈ parallelBox u tau q R W) :
    ∃ s ∈ Set.Icc (-R) R, dist x (latticeAxisPoint u tau q s) ≤ W*tau := by
  exact ⟨head (alignStem u x),abs_le.mp hx.1,(matching_axis_distance u x tau q).trans_le hx.2⟩

/-- Uniform physical boundedness of the entire endpoint-capped tube carrier. -/
theorem bounded_carrier_norm {k : ℕ} (T : UnitTube k) {δ width R : ℝ}
    (hδ1 : δ ≤ 1) (hw : 0 ≤ width) (hbase : ‖T.base‖ ≤ R)
    {x : Space k} (hx : x ∈ T.carrier (width*δ)) : ‖x‖ ≤ R+1+width := by
  obtain ⟨t,ht,hxt⟩ := hx
  have htbound : ‖t • T.direction‖ ≤ 1 := by
    rw [norm_smul,Real.norm_eq_abs,T.unit_direction,mul_one,abs_of_nonneg ht.1]
    exact ht.2
  have haxis : ‖T.axisPoint t‖ ≤ R+1 := (norm_add_le _ _).trans (add_le_add hbase htbound)
  have hnorm := norm_add_le (x-T.axisPoint t) (T.axisPoint t)
  rw [sub_add_cancel] at hnorm
  change ‖x-T.axisPoint t‖ ≤ width*δ at hxt
  nlinarith [mul_le_mul_of_nonneg_left hδ1 hw]

/-- A bounded actual tube is contained in one genuine finite-length O(tau)-wide
spatial box; the longitudinal bound is chosen before delta and tau. -/
theorem bounded_tube_spatial_box {k : ℕ} (u : Space (k+1)) (hu : ‖u‖ = 1)
    (T : UnitTube (k+1)) {δ tau width angular R : ℝ}
    (htau : 0 < tau) (hdr : δ ≤ tau) (hδ1 : δ ≤ 1)
    (hw : 0 ≤ width) (ha : 0 ≤ angular) (hbase : ‖T.base‖ ≤ R)
    (hcap : projectiveDistance T.direction u ≤ angular*tau) :
    T.carrier (width*δ) ⊆ parallelBox u tau (spatialLabel u tau T)
      (R+1+width) ((k:ℝ)+width+angular) := by
  intro x hx
  refine ⟨?_,tube_in_spatial_cylinder u hu T htau hdr hw ha hcap hx⟩
  have hhead : |head (alignStem u x)| ≤ ‖x‖ := by
    have h := PiLp.norm_apply_le (alignStem u x) (0 : Fin (k+1))
    simpa only [head,Real.norm_eq_abs,(alignStem u).norm_map] using h
  exact hhead.trans (bounded_carrier_norm T hδ1 hw hbase hx)

/-- The actual transverse angular normalization of one spatial box. -/
def normalizeBox {k : ℕ} (u : Space (k+1)) (tau : ℝ) (q : Cell k)
    (x : Space (k+1)) : Space (k+1) :=
  cons (head (alignStem u x)) (tau⁻¹ • (transverse u x-cellCenter (2*tau) q))

/-- The normalized transverse coordinate has a scale-independent width. -/
theorem normalizeBox_width {k : ℕ} (u : Space (k+1)) {tau R W : ℝ}
    (htau : 0 < tau) (q : Cell k) {x : Space (k+1)}
    (hx : x ∈ parallelBox u tau q R W) :
    |head (normalizeBox u tau q x)| ≤ R ∧ ‖tail (normalizeBox u tau q x)‖ ≤ W := by
  refine ⟨by simpa only [normalizeBox,head_cons] using hx.1,?_⟩
  rw [normalizeBox,tail_cons,norm_smul,Real.norm_eq_abs,abs_of_pos (inv_pos.mpr htau)]
  change tau⁻¹*dist (transverse u x) (cellCenter (2*tau) q) ≤ W
  have hp : dist (transverse u x) (cellCenter (2*tau) q) ≤ W*tau := hx.2
  have h : dist (transverse u x) (cellCenter (2*tau) q)/tau ≤ W := (div_le_iff₀ htau).mpr hp
  simpa only [div_eq_mul_inv,mul_comm] using h

end
end KakeyaFormal.SpatialAngular
