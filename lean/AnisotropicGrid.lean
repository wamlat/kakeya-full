import AnisotropicVolume
import GridShadingMeasure
import TubeVolume

/-! Genuine rounding of anisotropically transformed grid centers. A fiber has
O(1/tau) points, proved from exact volume scaling rather than ambient-dimensional
isotropic counting or an assumed lattice alignment. -/
namespace KakeyaFormal.AnisotropicGrid
open EuclideanSplit SpatialAngular AnisotropicRescaling AnisotropicVolume GridCells
open GridShadingMeasure TubeVolume MeasureTheory
open scoped ENNReal BigOperators
noncomputable section
open Classical

/-- The unique actual new-grid label of a transformed old-grid center. -/
def roundedLabel {k : ℕ} (u : Space (k+1)) (δ tau : ℝ) (q : Cell k)
    (z : Cell (k+1)) : Cell (k+1) :=
  label (δ/tau) (normalizeBox u tau q (cellCenter δ z))

/-- Actual Euclidean rounding error at the rescaled grid size. -/
theorem rounded_center_distance {k : ℕ} (u : Space (k+1)) {δ tau : ℝ}
    (hδ : 0 < δ) (htau : 0 < tau) (q : Cell k) (z : Cell (k+1)) :
    dist (normalizeBox u tau q (cellCenter δ z))
      (cellCenter (δ/tau) (roundedLabel u δ tau q z)) ≤ (k+1:ℝ)*(δ/tau)/2 := by
  simpa only [Nat.cast_add,Nat.cast_one,roundedLabel] using
    cell_center_distance (gridCell_covers (div_pos hδ htau)
      (normalizeBox u tau q (cellCenter δ z)))

/-- A fiber of rounded centers carries whole original cells into a ball at
exactly the rescaled grid size, including every cell boundary. -/
theorem fiber_image_subset_ball {k : ℕ} (u : Space (k+1)) (S : Finset (Cell (k+1)))
    {δ tau : ℝ} (hδ : 0 < δ) (htau : 0 < tau) (htau1 : tau ≤ 1)
    (q : Cell k) (z : Cell (k+1))
    (hfiber : ∀ y ∈ S, roundedLabel u δ tau q y = z) :
    normalizeBox u tau q '' cellUnion δ S ⊆
      Metric.closedBall (cellCenter (δ/tau) z) ((k+1:ℝ)*(δ/tau)) := by
  rintro x ⟨y,hy,rfl⟩
  have hlabel := (mem_cellUnion hδ S y).mp hy
  have hrnd := rounded_center_distance u hδ htau q (label δ y)
  rw [hfiber _ hlabel] at hrnd
  have hcell := cell_center_distance (gridCell_covers hδ y)
  have hmap := (normalizeBox_distance_bounds u htau htau1 q y (cellCenter δ (label δ y))).2
  have htri := dist_triangle (normalizeBox u tau q y)
    (normalizeBox u tau q (cellCenter δ (label δ y))) (cellCenter (δ/tau) z)
  have hdiv := div_le_div_of_nonneg_right hcell htau.le
  change dist (normalizeBox u tau q y) (cellCenter (δ/tau) z) ≤ _
  have halg : ((k+1:ℝ)*δ/2)/tau = (k+1:ℝ)*(δ/tau)/2 := by ring
  simp only [Nat.cast_add,Nat.cast_one] at hdiv
  rw [halg] at hdiv
  linarith

/-- Fixed geometric constant coming from the enclosing Euclidean ball. -/
def fiberConstant (k : ℕ) : ℝ := (k+1:ℝ)^(k+1)*unitBallVolume (k+1)

theorem fiberConstant_pos (k : ℕ) : 0 < fiberConstant k := by
  dsimp [fiberConstant]
  exact mul_pos (pow_pos (by positivity) _) (unitBallVolume_pos _)

/-- Actual anisotropic grid fibers contain at most C(k)/tau original cells.
The transverse Jacobian cancels all but one inverse power of tau. -/
theorem fiber_card_le {k : ℕ} (u : Space (k+1)) (S : Finset (Cell (k+1)))
    {δ tau : ℝ} (hδ : 0 < δ) (htau : 0 < tau) (htau1 : tau ≤ 1)
    (q : Cell k) (z : Cell (k+1))
    (hfiber : ∀ y ∈ S, roundedLabel u δ tau q y = z) :
    (S.card:ℝ) ≤ fiberConstant k/tau := by
  have hsub := fiber_image_subset_ball u S hδ htau htau1 q z hfiber
  have hfinite : (volume : Measure (Space (k+1)))
      (Metric.closedBall (cellCenter (δ/tau) z) ((k+1:ℝ)*(δ/tau))) ≠ ∞ :=
    (isCompact_closedBall (cellCenter (δ/tau) z) ((k+1:ℝ)*(δ/tau))).measure_lt_top.ne
  have hm := measureReal_mono hsub hfinite
  rw [normalizeBox_realVolume u htau,cellUnion_volume hδ,
    ball_volume_scale _ (by positivity)] at hm
  have halg : ((k+1:ℝ)*(δ/tau))^(k+1)*unitBallVolume (k+1) =
      (δ^(k+1)/tau^k)*(fiberConstant k/tau) := by
    dsimp [fiberConstant]
    rw [mul_pow,div_pow,pow_succ tau]
    field_simp
  rw [halg] at hm
  have hfactor : 0 < δ^(k+1)/tau^k := div_pos (pow_pos hδ _) (pow_pos htau _)
  apply (mul_le_mul_iff_right₀ hfactor).mp
  calc
    (δ^(k+1)/tau^k)*(S.card:ℝ) = δ^(k+1)*(S.card:ℝ)/tau^k := by ring
    _ ≤ (δ^(k+1)/tau^k)*(fiberConstant k/tau) := hm

/-- The constructed actual fiber of any finite old cell set obeys that bound. -/
theorem rounded_fiber_count {k : ℕ} (u : Space (k+1)) (S : Finset (Cell (k+1)))
    {δ tau : ℝ} (hδ : 0 < δ) (htau : 0 < tau) (htau1 : tau ≤ 1)
    (q : Cell k) (z : Cell (k+1)) :
    ((S.filter (fun y => roundedLabel u δ tau q y = z)).card:ℝ) ≤ fiberConstant k/tau :=
  fiber_card_le u _ hδ htau htau1 q z (fun _y hy => (Finset.mem_filter.mp hy).2)

/-- Actual occupied new-grid labels retain the correct factor tau in cardinality. -/
theorem rounded_count_lower {k : ℕ} (u : Space (k+1)) (S : Finset (Cell (k+1)))
    {δ tau : ℝ} (hδ : 0 < δ) (htau : 0 < tau) (htau1 : tau ≤ 1) (q : Cell k) :
    (S.card:ℝ)*tau/fiberConstant k ≤ ((S.image (roundedLabel u δ tau q)).card:ℝ) := by
  have hsum : (S.card:ℝ) = ∑ z ∈ S.image (roundedLabel u δ tau q),
      ((S.filter (fun y => roundedLabel u δ tau q y = z)).card:ℝ) := by
    have hh := Finset.sum_fiberwise_of_maps_to (s := S) (t := S.image (roundedLabel u δ tau q))
      (g := roundedLabel u δ tau q) (fun y hy => Finset.mem_image.mpr ⟨y,hy,rfl⟩) (fun _ => (1:ℝ))
    simpa using hh.symm
  have hbound : (S.card:ℝ) ≤ ((S.image (roundedLabel u δ tau q)).card:ℝ)*(fiberConstant k/tau) := by
    rw [hsum]
    have hh := Finset.sum_le_sum (s := S.image (roundedLabel u δ tau q))
      (fun z _ => rounded_fiber_count u S hδ htau htau1 q z)
    simpa only [Finset.sum_const,nsmul_eq_mul] using hh
  apply (div_le_iff₀ (fiberConstant_pos k)).mpr
  have hh := mul_le_mul_of_nonneg_right hbound htau.le
  have heq : (((S.image (roundedLabel u δ tau q)).card:ℝ)*(fiberConstant k/tau))*tau =
      ((S.image (roundedLabel u δ tau q)).card:ℝ)*fiberConstant k := by field_simp
  rwa [heq] at hh

/-- Rounded actual centers are carried by the explicit finite cover of unit tubes,
with only the usual dimension-dependent rounding width enlargement. -/
theorem rounded_center_carrier {k : ℕ} (u : Space (k+1)) (q : Cell k)
    (T : UnitTube (k+1)) {tau angular width δ : ℝ}
    (hu : ‖u‖ = 1) (hδ : 0 < δ) (htau : 0 < tau) (htau1 : tau ≤ 1)
    (hcap : projectiveDistance T.direction u ≤ angular*tau)
    (z : Cell (k+1)) (hz : cellCenter δ z ∈ T.carrier (width*δ)) :
    ∃ j ∈ Finset.range (Nat.ceil (1+angular)+1),
      cellCenter (δ/tau) (roundedLabel u δ tau q z) ∈
        (transformedTube u htau.ne' q T j).carrier ((width+(k+1:ℝ)/2)*(δ/tau)) := by
  obtain ⟨j,hj,t,ht,hd⟩ := transformed_carrier_unit_cover u q T hu htau htau1 hcap hz
  refine ⟨j,hj,t,ht,?_⟩
  have hrnd := rounded_center_distance u hδ htau q z
  have htri := dist_triangle (cellCenter (δ/tau) (roundedLabel u δ tau q z))
    (normalizeBox u tau q (cellCenter δ z)) ((transformedTube u htau.ne' q T j).axisPoint t)
  rw [dist_comm (cellCenter (δ/tau) (roundedLabel u δ tau q z))
    (normalizeBox u tau q (cellCenter δ z))] at htri
  nlinarith

end
end KakeyaFormal.AnisotropicGrid
