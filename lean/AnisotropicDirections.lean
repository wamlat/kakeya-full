import AnisotropicRescaling

/-! Quantitative projective direction normalization under the actual transverse
dilation. Constants depend on angular width, not the changing box scale. -/
namespace KakeyaFormal.AnisotropicDirections
open EuclideanSplit PivotDirections SpatialAngular AnisotropicRescaling ProjectiveGeometry LiftGraph
noncomputable section

theorem compress_add {k : ℕ} (tau : ℝ) (x y : Space (k+1)) :
    compress tau (x+y) = compress tau x+compress tau y := by
  simp [compress,smul_add,cons_add]

theorem compress_smul {k : ℕ} (tau a : ℝ) (x : Space (k+1)) :
    compress tau (a • x) = a • compress tau x := by
  simp [compress,smul_smul,← cons_smul,mul_comm]

theorem compress_sub {k : ℕ} (tau : ℝ) (x y : Space (k+1)) :
    compress tau (x-y) = compress tau x-compress tau y := by
  ext i
  cases i using Fin.cases <;> simp [compress,cons,head,tail]
  all_goals ring

theorem unitize_neg {k : ℕ} (x : Space k) : unitize (-x) = -unitize x := by
  simp [unitize]

/-- The usual relative-error normalization bound also holds projectively. -/
theorem projective_unitize {k : ℕ} (x y : Space k) (hx : x ≠ 0) (hy : y ≠ 0) :
    projectiveDistance (unitize x) (unitize y) ≤ 2*projectiveDistance x y/‖y‖ := by
  by_cases h : ‖x-y‖ ≤ ‖x+y‖
  · simp only [projectiveDistance,min_eq_left h]
    exact (min_le_left _ _).trans (unitize_perturbation x y hx hy)
  · have hh := unitize_perturbation x (-y) hx (neg_ne_zero.mpr hy)
    simp only [unitize_neg,sub_neg_eq_add,norm_neg] at hh
    simp only [projectiveDistance,min_eq_right (le_of_not_ge h)]
    exact (min_le_right _ _).trans hh

/-- An orthogonal frame preserves the actual unoriented chord distance. -/
theorem frame_projective {k : ℕ} (u v w : Space (k+1)) :
    projectiveDistance (alignStem u v) (alignStem u w) = projectiveDistance v w := by
  simp only [projectiveDistance,← map_sub,← map_add,(alignStem u).norm_map]

/-- The inverse linear dilation is projectively nonexpanding before unit normalization. -/
theorem compress_projective {k : ℕ} {tau : ℝ} (htau : 0 ≤ tau) (htau1 : tau ≤ 1)
    (v w : Space (k+1)) :
    projectiveDistance (compress tau v) (compress tau w) ≤ projectiveDistance v w := by
  unfold projectiveDistance
  rw [← compress_sub,← compress_add]
  exact min_le_min (compress_norm_le htau htau1 _) (compress_norm_le htau htau1 _)

/-- Inverse compression of a normalized transformed vector is the stated
positive multiple of the original framed unit direction. -/
theorem compress_transformed {k : ℕ} (u v : Space (k+1)) {tau : ℝ} (htau : tau ≠ 0) :
    compress tau (transformedDirection u tau v) =
      ‖directionVector u tau v‖⁻¹ • alignStem u v := by
  rw [transformedDirection,unitize,compress_smul]
  simp only [directionVector,compress_stretch htau]

theorem unitize_compress_transformed {k : ℕ} (u v : Space (k+1)) {tau : ℝ}
    (htau : tau ≠ 0) (hv : ‖v‖ = 1) :
    unitize (compress tau (transformedDirection u tau v)) = alignStem u v := by
  rw [compress_transformed u v htau]
  exact unitize_pos_smul _ (by rw [(alignStem u).norm_map,hv])
    (inv_pos.mpr (norm_pos_iff.mpr (directionVector_nonzero u htau v hv)))

theorem norm_compress_transformed {k : ℕ} (u v : Space (k+1)) {tau : ℝ}
    (htau : tau ≠ 0) (hv : ‖v‖ = 1) :
    ‖compress tau (transformedDirection u tau v)‖ = ‖directionVector u tau v‖⁻¹ := by
  rw [compress_transformed u v htau,norm_smul,Real.norm_eq_abs,
    abs_of_nonneg (inv_nonneg.mpr (norm_nonneg _)),(alignStem u).norm_map,hv,mul_one]

/-- A coarse inverse direction bound valid at every tau; the sharper tau factor
will follow from the local angular chart. -/
theorem transformed_projective_inverse_coarse {k : ℕ} (u v w : Space (k+1))
    {tau angular : ℝ} (hu : ‖u‖ = 1) (hv : ‖v‖ = 1) (hw : ‖w‖ = 1)
    (htau : 0 < tau) (htau1 : tau ≤ 1)
    (hwcap : projectiveDistance w u ≤ angular*tau) :
    projectiveDistance v w ≤ 2*(1+angular)*
      projectiveDistance (transformedDirection u tau v) (transformedDirection u tau w) := by
  have hnorm (z : Space (k+1)) (hz : ‖z‖ = 1) :
      0 < ‖compress tau (transformedDirection u tau z)‖ := by
    rw [norm_compress_transformed u z htau.ne' hz]
    exact inv_pos.mpr (norm_pos_iff.mpr (directionVector_nonzero u htau.ne' z hz))
  have h := projective_unitize (compress tau (transformedDirection u tau v))
    (compress tau (transformedDirection u tau w))
    (norm_pos_iff.mp (hnorm v hv)) (norm_pos_iff.mp (hnorm w hw))
  rw [unitize_compress_transformed u v htau.ne' hv,
    unitize_compress_transformed u w htau.ne' hw,frame_projective,
    norm_compress_transformed u w htau.ne' hw,div_inv_eq_mul] at h
  have hcomp := compress_projective htau.le htau1
    (transformedDirection u tau v) (transformedDirection u tau w)
  have hs := (directionVector_speed u w hu hw htau htau1 hwcap).2
  have hp : 0 ≤ projectiveDistance (transformedDirection u tau v) (transformedDirection u tau w) :=
    le_min (norm_nonneg _) (norm_nonneg _)
  calc
    _ ≤ 2*projectiveDistance (compress tau (transformedDirection u tau v))
        (compress tau (transformedDirection u tau w))*‖directionVector u tau w‖ := h
    _ ≤ 2*projectiveDistance (transformedDirection u tau v)
        (transformedDirection u tau w)*‖directionVector u tau w‖ :=
      mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hcomp (by norm_num)) (norm_nonneg _)
    _ ≤ 2*projectiveDistance (transformedDirection u tau v)
        (transformedDirection u tau w)*(1+angular) :=
      mul_le_mul_of_nonneg_left hs (by positivity)
    _ = _ := by ring

/-- Positive scalar multiplication does not change a normalized vector. -/
theorem unitize_positive_scale {k : ℕ} (x : Space k) {a : ℝ} (ha : 0 < a) :
    unitize (a • x) = unitize x := by
  simp only [unitize,norm_smul,Real.norm_eq_abs,abs_of_pos ha,smul_smul,mul_inv_rev]
  congr 1
  field_simp

/-- The graph-chart slope of a vector with nonzero head. -/
def graphSlope {k : ℕ} (x : Space (k+1)) : Space k := (head x)⁻¹ • tail x

/-- Exact algebra linking a nonzero-head vector to its graph coordinates. -/
theorem graphSlope_cons {k : ℕ} (x : Space (k+1)) (hx : head x ≠ 0) :
    cons 1 (graphSlope x) = (head x)⁻¹ • x := by
  rw [← cons_head_tail x,← cons_smul]
  simp only [head_cons,tail_cons,graphSlope,inv_mul_cancel₀ hx]

/-- The graph-chart representative differs from the normalized actual vector
only by its projectively irrelevant sign. -/
theorem graphSlope_representative {k : ℕ} (x : Space (k+1)) (hx : head x ≠ 0) :
    graphDirection (graphSlope x) = unitize x ∨
      graphDirection (graphSlope x) = -unitize x := by
  rw [graphDirection,graphSlope_cons x hx]
  rcases lt_or_gt_of_ne hx with hneg | hpos
  · right
    have hi : 0 < -(head x)⁻¹ := neg_pos.mpr (inv_lt_zero.mpr hneg)
    have heq : (head x)⁻¹ • x = -((-(head x)⁻¹) • x) := by simp
    rw [heq,unitize_neg,unitize_positive_scale x hi]
  · left
    exact unitize_positive_scale x (inv_pos.mpr hpos)

/-- Graph slopes preserve the precise projective relationship of the actual vectors. -/
theorem graphSlope_projective {k : ℕ} (x y : Space (k+1))
    (hx : head x ≠ 0) (hy : head y ≠ 0) :
    projectiveDistance (graphDirection (graphSlope x)) (graphDirection (graphSlope y)) =
      projectiveDistance (unitize x) (unitize y) := by
  rcases graphSlope_representative x hx with hx' | hx' <;>
    rcases graphSlope_representative y hy with hy' | hy' <;>
    rw [hx',hy'] <;> simp only [projective_neg_left,projectiveDistance_neg_right]

/-- Dilation multiplies graph slope by exactly tau inverse. -/
theorem graphSlope_stretch {k : ℕ} (tau : ℝ) (x : Space (k+1)) :
    graphSlope (stretch tau x) = tau⁻¹ • graphSlope x := by
  simp [graphSlope,stretch,smul_smul,mul_comm]

theorem graphSlope_recover {k : ℕ} {tau : ℝ} (htau : tau ≠ 0) (x : Space (k+1)) :
    tau • graphSlope (stretch tau x) = graphSlope x := by
  rw [graphSlope_stretch,smul_smul,mul_inv_cancel₀ htau,one_smul]

/-- A sufficiently narrow projective angular cap stays in the actual nonzero-head chart. -/
theorem angular_head_lower {k : ℕ} (u v : Space (k+1)) {tau angular : ℝ}
    (hu : ‖u‖ = 1) (hv : ‖v‖ = 1)
    (hcap : projectiveDistance v u ≤ angular*tau) (hsmall : angular*tau ≤ 1/2) :
    1/2 ≤ |head (alignStem u v)| := by
  have htail : ‖tail (alignStem u v)‖ ≤ 1/2 :=
    ((transverse_direction_le u v hu).trans hcap).trans hsmall
  have hs := norm_sq_split (alignStem u v)
  rw [(alignStem u).norm_map,hv] at hs
  nlinarith [norm_nonneg (tail (alignStem u v)),abs_nonneg (head (alignStem u v)),
    sq_abs (head (alignStem u v))]

/-- Actual dilated graph slopes remain in a fixed bounded region. -/
theorem transformed_slope_bound {k : ℕ} (u v : Space (k+1)) {tau angular : ℝ}
    (hu : ‖u‖ = 1) (hv : ‖v‖ = 1) (htau : 0 < tau) (_ha : 0 ≤ angular)
    (hcap : projectiveDistance v u ≤ angular*tau) (hsmall : angular*tau ≤ 1/2) :
    ‖graphSlope (directionVector u tau v)‖ ≤ 2*angular := by
  have hh := angular_head_lower u v hu hv hcap hsmall
  have hhpos : 0 < |head (alignStem u v)| := by linarith
  have hcoef : |head (alignStem u v)|⁻¹ ≤ 2 := by
    rw [← one_div]
    exact (div_le_iff₀ hhpos).mpr (by linarith)
  have htail : ‖tail (alignStem u v)‖ ≤ angular*tau :=
    (transverse_direction_le u v hu).trans hcap
  have hscaled : tau⁻¹*‖tail (alignStem u v)‖ ≤ angular := by
    calc
      _ ≤ tau⁻¹*(angular*tau) := mul_le_mul_of_nonneg_left htail (inv_nonneg.mpr htau.le)
      _ = _ := by field_simp
  simp only [graphSlope,directionVector,stretch,head_cons,tail_cons,norm_smul,
    Real.norm_eq_abs,abs_inv,abs_of_pos htau]
  exact mul_le_mul hcoef hscaled (by positivity) (by norm_num)

/-- On a narrow angular chart, the actual inverse projective map gains the
full factor tau. Both signs of each original direction are included. -/
theorem transformed_projective_inverse_small {k : ℕ} (u v w : Space (k+1))
    {tau angular : ℝ} (hu : ‖u‖ = 1) (hv : ‖v‖ = 1) (hw : ‖w‖ = 1)
    (htau : 0 < tau) (ha : 0 ≤ angular)
    (hvcap : projectiveDistance v u ≤ angular*tau)
    (hwcap : projectiveDistance w u ≤ angular*tau) (hsmall : angular*tau ≤ 1/2) :
    projectiveDistance v w ≤ 4*(1+2*angular)^2*tau*
      projectiveDistance (transformedDirection u tau v) (transformedDirection u tau w) := by
  let p := graphSlope (directionVector u tau v)
  let q := graphSlope (directionVector u tau w)
  have hhead (z : Space (k+1)) (hz : ‖z‖ = 1)
      (hcap : projectiveDistance z u ≤ angular*tau) : head (alignStem u z) ≠ 0 := by
    have hh := angular_head_lower u z hu hz hcap hsmall
    intro heq
    simp only [heq,abs_zero] at hh
    norm_num at hh
  have hvhead := hhead v hv hvcap
  have hwhead := hhead w hw hwcap
  have hframe (z : Space (k+1)) (hz : ‖z‖ = 1) : unitize (alignStem u z) = alignStem u z := by
    simp only [unitize,(alignStem u).norm_map,hz,inv_one,one_smul]
  have hrec (z : Space (k+1)) :
      tau • graphSlope (directionVector u tau z) = graphSlope (alignStem u z) :=
    graphSlope_recover htau.ne' _
  have horig : projectiveDistance (graphDirection (tau • p)) (graphDirection (tau • q)) =
      projectiveDistance v w := by
    dsimp only [p,q]
    rw [hrec v,hrec w,graphSlope_projective _ _ hvhead hwhead,
      hframe v hv,hframe w hw,frame_projective]
  have hnew : projectiveDistance (graphDirection p) (graphDirection q) =
      projectiveDistance (transformedDirection u tau v) (transformedDirection u tau w) := by
    apply graphSlope_projective
    · simpa only [directionVector,stretch,head_cons] using hvhead
    · simpa only [directionVector,stretch,head_cons] using hwhead
  have hforward := graphDirection_forward (tau • p) (tau • q)
  rw [horig,← smul_sub,norm_smul,Real.norm_eq_abs,abs_of_pos htau] at hforward
  have hinv := graphDirection_inverse p q (show 0 ≤ 2*angular by positivity)
    (transformed_slope_bound u v hu hv htau ha hvcap hsmall)
    (transformed_slope_bound u w hu hw htau ha hwcap hsmall)
  rw [hnew] at hinv
  have hh := mul_le_mul_of_nonneg_left hinv (show 0 ≤ 2*tau by positivity)
  nlinarith

/-- Uniform inverse estimate for the entire scale range. The constant depends
only on the fixed angular width; there is no power of tau in the cap coefficient. -/
theorem transformed_projective_inverse {k : ℕ} (u v w : Space (k+1))
    {tau angular : ℝ} (hu : ‖u‖ = 1) (hv : ‖v‖ = 1) (hw : ‖w‖ = 1)
    (htau : 0 < tau) (htau1 : tau ≤ 1) (ha : 0 ≤ angular)
    (hvcap : projectiveDistance v u ≤ angular*tau)
    (hwcap : projectiveDistance w u ≤ angular*tau) :
    projectiveDistance v w ≤ 4*(1+2*angular)^2*tau*
      projectiveDistance (transformedDirection u tau v) (transformedDirection u tau w) := by
  by_cases hsmall : angular*tau ≤ 1/2
  · exact transformed_projective_inverse_small u v w hu hv hw htau ha hvcap hwcap hsmall
  · have hcoarse := transformed_projective_inverse_coarse u v w hu hv hw htau htau1 hwcap
    have hlarge : 1 ≤ 2*angular*tau := by linarith
    have hcoef : 2*(1+angular) ≤ 4*(1+2*angular)^2*tau := by
      have h1 := mul_le_mul_of_nonneg_left hlarge (show 0 ≤ 2*(1+angular) by positivity)
      have h2 := mul_le_mul_of_nonneg_right
        (show angular*(1+angular) ≤ (1+2*angular)^2 by nlinarith) (show 0 ≤ 4*tau by positivity)
      nlinarith
    exact hcoarse.trans (mul_le_mul_of_nonneg_right hcoef
      (le_min (norm_nonneg _) (norm_nonneg _)))

/-- Actual original separated directions stay separated at the rescaled rate. -/
theorem transformed_direction_separation {k : ℕ} (u v w : Space (k+1))
    {tau angular s : ℝ} (hu : ‖u‖ = 1) (hv : ‖v‖ = 1) (hw : ‖w‖ = 1)
    (htau : 0 < tau) (htau1 : tau ≤ 1) (ha : 0 ≤ angular)
    (hvcap : projectiveDistance v u ≤ angular*tau)
    (hwcap : projectiveDistance w u ≤ angular*tau)
    (hsep : s ≤ projectiveDistance v w) :
    s/(4*(1+2*angular)^2*tau) ≤
      projectiveDistance (transformedDirection u tau v) (transformedDirection u tau w) := by
  have hC : 0 < 4*(1+2*angular)^2*tau := by positivity
  apply (div_le_iff₀ hC).mpr
  simpa only [mul_comm] using hsep.trans
    (transformed_projective_inverse u v w hu hv hw htau htau1 ha hvcap hwcap)

end
end KakeyaFormal.AnisotropicDirections
