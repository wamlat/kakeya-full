import SpatialAngular
import LiftGraph

/-! Actual anisotropic normalization of one angular/spatial box. The head
coordinate is fixed and the transverse coordinates are divided by tau. -/
namespace KakeyaFormal.AnisotropicRescaling
open KakeyaFormal.EuclideanSplit KakeyaFormal.PivotDirections KakeyaFormal.SpatialAngular
noncomputable section

/-- Genuine transverse dilation, before orthogonal framing and translation. -/
def stretch {k : ℕ} (tau : ℝ) (x : Space (k+1)) : Space (k+1) :=
  cons (head x) (tau⁻¹ • tail x)

/-- Its explicit inverse contracts the transverse coordinates. -/
def compress {k : ℕ} (tau : ℝ) (x : Space (k+1)) : Space (k+1) :=
  cons (head x) (tau • tail x)

theorem stretch_add {k : ℕ} (tau : ℝ) (x y : Space (k+1)) :
    stretch tau (x+y) = stretch tau x+stretch tau y := by
  simp [stretch,smul_add,cons_add]

theorem stretch_smul {k : ℕ} (tau a : ℝ) (x : Space (k+1)) :
    stretch tau (a • x) = a • stretch tau x := by
  simp [stretch,smul_smul,← cons_smul,mul_comm]

theorem stretch_sub {k : ℕ} (tau : ℝ) (x y : Space (k+1)) :
    stretch tau (x-y) = stretch tau x-stretch tau y := by
  ext i
  cases i using Fin.cases <;> simp [stretch,cons,head,tail]
  all_goals ring

theorem stretch_zero {k : ℕ} (tau : ℝ) : stretch tau (0 : Space (k+1)) = 0 := by
  simp [stretch]

theorem compress_stretch {k : ℕ} {tau : ℝ} (htau : tau ≠ 0) (x : Space (k+1)) :
    compress tau (stretch tau x) = x := by
  simp [compress,stretch,smul_smul,htau]

theorem stretch_compress {k : ℕ} {tau : ℝ} (htau : tau ≠ 0) (x : Space (k+1)) :
    stretch tau (compress tau x) = x := by
  simp [compress,stretch,smul_smul,htau]

theorem stretch_injective {k : ℕ} {tau : ℝ} (htau : tau ≠ 0) :
    Function.Injective (@stretch k tau) := by
  intro x y hxy
  have h := congrArg (compress tau) hxy
  simpa only [compress_stretch htau] using h

/-- Contracting the transverse coordinates is a Euclidean contraction. -/
theorem compress_norm_le {k : ℕ} {tau : ℝ} (htau : 0 ≤ tau) (htau1 : tau ≤ 1)
    (x : Space (k+1)) : ‖compress tau x‖ ≤ ‖x‖ := by
  have hs := norm_sq_split (compress tau x)
  simp only [compress,head_cons,tail_cons,norm_smul,Real.norm_eq_abs,abs_of_nonneg htau] at hs
  have hx := norm_sq_split x
  have htail : tau*‖tail x‖ ≤ ‖tail x‖ := by
    simpa only [one_mul] using mul_le_mul_of_nonneg_right htau1 (norm_nonneg _)
  change ‖cons (head x) (tau • tail x)‖ ≤ ‖x‖
  nlinarith [norm_nonneg (cons (head x) (tau • tail x)),norm_nonneg x,norm_nonneg (tail x),
    mul_nonneg htau (norm_nonneg (tail x))]

/-- Transverse dilation expands no distance by less than1 or more than1/tau. -/
theorem stretch_norm_bounds {k : ℕ} {tau : ℝ} (htau : 0 < tau) (htau1 : tau ≤ 1)
    (x : Space (k+1)) : ‖x‖ ≤ ‖stretch tau x‖ ∧ ‖stretch tau x‖ ≤ ‖x‖/tau := by
  constructor
  · have h := compress_norm_le htau.le htau1 (stretch tau x)
    simpa only [compress_stretch htau.ne'] using h
  · have hcontract : ‖cons (tau*head x) (tail x)‖ ≤ ‖x‖ := by
      have hs := norm_sq_split (cons (tau*head x) (tail x))
      simp only [head_cons,tail_cons] at hs
      have hx := norm_sq_split x
      have hh : |tau*head x| ≤ |head x| := by
        rw [abs_mul,abs_of_pos htau]
        simpa only [one_mul] using mul_le_mul_of_nonneg_right htau1 (abs_nonneg (head x))
      nlinarith [sq_abs (tau*head x),sq_abs (head x),abs_nonneg (tau*head x),abs_nonneg (head x),
        norm_nonneg (cons (tau*head x) (tail x)),norm_nonneg x]
    have heq : tau • stretch tau x = cons (tau*head x) (tail x) := by
      simp [stretch,← cons_smul,smul_smul,htau.ne']
    rw [← heq,norm_smul,Real.norm_eq_abs,abs_of_pos htau] at hcontract
    exact (le_div_iff₀ htau).mpr (by simpa only [mul_comm] using hcontract)

/-- Actual distance transformation, with the Euclidean norms and anisotropic rate. -/
theorem stretch_distance_bounds {k : ℕ} {tau : ℝ} (htau : 0 < tau) (htau1 : tau ≤ 1)
    (x y : Space (k+1)) :
    dist x y ≤ dist (stretch tau x) (stretch tau y) ∧
      dist (stretch tau x) (stretch tau y) ≤ dist x y/tau := by
  simpa only [dist_eq_norm,← stretch_sub] using stretch_norm_bounds htau htau1 (x-y)

/-- Orthogonal framing followed by genuine transverse dilation. -/
def directionVector {k : ℕ} (u : Space (k+1)) (tau : ℝ) (v : Space (k+1)) : Space (k+1) :=
  stretch tau (alignStem u v)

/-- An original unit direction has a nonzero actual transformed velocity. -/
theorem directionVector_nonzero {k : ℕ} (u : Space (k+1)) {tau : ℝ}
    (htau : tau ≠ 0) (v : Space (k+1)) (hv : ‖v‖ = 1) : directionVector u tau v ≠ 0 := by
  intro hz
  have hzero : stretch tau (alignStem u v) = stretch tau 0 := by simpa only [directionVector,stretch_zero] using hz
  have h := stretch_injective htau hzero
  have hn := congrArg norm h
  rw [(alignStem u).norm_map,norm_zero,hv] at hn
  norm_num at hn

/-- Actual normalized transformed direction. -/
def transformedDirection {k : ℕ} (u : Space (k+1)) (tau : ℝ) (v : Space (k+1)) : Space (k+1) :=
  unitize (directionVector u tau v)

theorem transformedDirection_unit {k : ℕ} (u : Space (k+1)) {tau : ℝ}
    (htau : tau ≠ 0) (v : Space (k+1)) (hv : ‖v‖ = 1) :
    ‖transformedDirection u tau v‖ = 1 :=
  unitize_unit _ (directionVector_nonzero u htau v hv)

/-- Normalized spatial-box coordinates are the stated affine dilation exactly. -/
theorem normalizeBox_affine {k : ℕ} (u x : Space (k+1)) (tau : ℝ) (q : Cell k) :
    normalizeBox u tau q x = stretch tau (alignStem u x)-cons 0 (tau⁻¹ • cellCenter (2*tau) q) := by
  simp only [normalizeBox,stretch,transverse,smul_sub]
  ext i
  cases i using Fin.cases <;> simp [cons,head,tail]

theorem normalizeBox_distance_bounds {k : ℕ} (u : Space (k+1)) {tau : ℝ}
    (htau : 0 < tau) (htau1 : tau ≤ 1) (q : Cell k) (x y : Space (k+1)) :
    dist x y ≤ dist (normalizeBox u tau q x) (normalizeBox u tau q y) ∧
      dist (normalizeBox u tau q x) (normalizeBox u tau q y) ≤ dist x y/tau := by
  simp only [normalizeBox_affine,dist_sub_right]
  have h := stretch_distance_bounds htau htau1 (alignStem u x) (alignStem u y)
  simpa only [(alignStem u).dist_map] using h

/-- The Euclidean norm is bounded by the sum of head and tail lengths. -/
theorem norm_cons_le {k : ℕ} (a : ℝ) (x : Space k) :
    ‖cons a x‖ ≤ |a|+‖x‖ := by
  have heq : cons a x = cons a 0+cons 0 x := by simp [← cons_add]
  rw [heq]
  simpa only [norm_cons_axis,norm_cons_zero] using norm_add_le (cons a 0) (cons 0 x)

/-- Dilation of a direction in the angular box produces a segment of uniformly
bounded length, even when the box scale tends to zero. -/
theorem directionVector_speed {k : ℕ} (u v : Space (k+1))
    {tau angular : ℝ} (hu : ‖u‖ = 1) (hv : ‖v‖ = 1)
    (htau : 0 < tau) (htau1 : tau ≤ 1)
    (hcap : projectiveDistance v u ≤ angular*tau) :
    1 ≤ ‖directionVector u tau v‖ ∧ ‖directionVector u tau v‖ ≤ 1+angular := by
  have hframe : ‖alignStem u v‖ = 1 := by rw [(alignStem u).norm_map,hv]
  constructor
  · simpa only [directionVector,hframe] using
      (stretch_norm_bounds htau htau1 (alignStem u v)).1
  · have htail : ‖tail (alignStem u v)‖ ≤ angular*tau :=
      (transverse_direction_le u v hu).trans hcap
    have hhead : |head (alignStem u v)| ≤ 1 := by
      have hs := norm_sq_split (alignStem u v)
      rw [hframe] at hs
      nlinarith [sq_abs (head (alignStem u v)),sq_nonneg ‖tail (alignStem u v)‖,
        abs_nonneg (head (alignStem u v))]
    have htail' : ‖tau⁻¹ • tail (alignStem u v)‖ ≤ angular := by
      rw [norm_smul,Real.norm_eq_abs,abs_of_pos (inv_pos.mpr htau)]
      calc
        _ ≤ tau⁻¹*(angular*tau) := mul_le_mul_of_nonneg_left htail (inv_nonneg.mpr htau.le)
        _ = angular := by field_simp
    exact (norm_cons_le _ _).trans (add_le_add hhead htail')

/-- The speed times the normalized direction is the original transformed velocity. -/
theorem speed_smul_transformedDirection {k : ℕ} (u v : Space (k+1))
    {tau : ℝ} (htau : tau ≠ 0) (hv : ‖v‖ = 1) :
    ‖directionVector u tau v‖ • transformedDirection u tau v = directionVector u tau v := by
  have hn := norm_ne_zero_iff.mpr (directionVector_nonzero u htau v hv)
  simp only [transformedDirection,unitize,smul_smul,mul_inv_cancel₀ hn,one_smul]

/-- The actual affine map sends every original axis point to its exact dilated axis point. -/
theorem normalizeBox_axisPoint {k : ℕ} (u : Space (k+1)) (tau : ℝ) (q : Cell k)
    (T : UnitTube (k+1)) (t : ℝ) :
    normalizeBox u tau q (T.axisPoint t) =
      normalizeBox u tau q T.base+t • directionVector u tau T.direction := by
  simp only [normalizeBox_affine,UnitTube.axisPoint,map_add,map_smul,stretch_add,stretch_smul,
    directionVector]
  abel

/-- Actual unit tubes covering the dilated segment: their starts are integer
parameters along its transformed unit direction. -/
def transformedTube {k : ℕ} (u : Space (k+1)) {tau : ℝ} (htau : tau ≠ 0)
    (q : Cell k) (T : UnitTube (k+1)) (j : ℕ) : UnitTube (k+1) where
  base := normalizeBox u tau q T.base+(j:ℝ) • transformedDirection u tau T.direction
  direction := transformedDirection u tau T.direction
  unit_direction := transformedDirection_unit u htau T.direction T.unit_direction

/-- Every parameter in a bounded segment belongs to an actual integer unit interval. -/
theorem finite_unit_interval_cover {L s : ℝ} (hs : s ∈ Set.Icc (0:ℝ) L) :
    ∃ j ∈ Finset.range (Nat.ceil L+1), ∃ t ∈ Set.Icc (0:ℝ) 1, s=(j:ℝ)+t := by
  let j := Nat.floor s
  have hjlo : (j:ℝ) ≤ s := Nat.floor_le hs.1
  have hjhi : s < (j:ℝ)+1 := Nat.lt_floor_add_one s
  have hjbound : (j:ℝ) ≤ (Nat.ceil L:ℝ) := hjlo.trans (hs.2.trans (Nat.le_ceil L))
  have hjnat : j ≤ Nat.ceil L := by exact_mod_cast hjbound
  exact ⟨j,Finset.mem_range_succ_iff.mpr hjnat,s-(j:ℝ),⟨by linarith,by linarith⟩,by ring⟩

/-- The dilated carrier is covered by a fixed finite number of actual unit tubes.
The index range depends on the angular width, never on tau or delta. -/
theorem transformed_carrier_unit_cover {k : ℕ} (u : Space (k+1)) (q : Cell k)
    (T : UnitTube (k+1)) {tau angular width δ : ℝ}
    (hu : ‖u‖ = 1) (htau : 0 < tau) (htau1 : tau ≤ 1)
    (hcap : projectiveDistance T.direction u ≤ angular*tau)
    {x : Space (k+1)} (hx : x ∈ T.carrier (width*δ)) :
    ∃ j ∈ Finset.range (Nat.ceil (1+angular)+1),
      normalizeBox u tau q x ∈ (transformedTube u htau.ne' q T j).carrier (width*(δ/tau)) := by
  rcases hx with ⟨t,ht,hnear⟩
  have hs := directionVector_speed u T.direction hu T.unit_direction htau htau1 hcap
  have hp : ‖directionVector u tau T.direction‖*t ∈ Set.Icc (0:ℝ) (1+angular) :=
    ⟨mul_nonneg (norm_nonneg _) ht.1,
      (mul_le_mul_of_nonneg_left ht.2 (norm_nonneg _)).trans (by simpa using hs.2)⟩
  obtain ⟨j,hj,s,hspar,hparam⟩ := finite_unit_interval_cover hp
  refine ⟨j,hj,s,hspar,?_⟩
  have haxis : (transformedTube u htau.ne' q T j).axisPoint s =
      normalizeBox u tau q (T.axisPoint t) := by
    rw [normalizeBox_axisPoint]
    change (normalizeBox u tau q T.base+(j:ℝ) • transformedDirection u tau T.direction)+
      s • transformedDirection u tau T.direction = _
    rw [add_assoc,← add_smul,← hparam,mul_smul]
    rw [smul_comm, speed_smul_transformedDirection u T.direction htau.ne' T.unit_direction]
  rw [haxis]
  calc
    _ ≤ dist x (T.axisPoint t)/tau :=
      (normalizeBox_distance_bounds u htau htau1 q x (T.axisPoint t)).2
    _ ≤ (width*δ)/tau := div_le_div_of_nonneg_right hnear htau.le
    _ = _ := by ring

end
end KakeyaFormal.AnisotropicRescaling
