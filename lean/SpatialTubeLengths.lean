import SpatialTubeCover

/-! Direct spatial containment for actual variable-length axes. The original
tube bases, directions, scales and spatial labels are unchanged. Only the fixed
cover constants depend on the prescribed upper length. -/
namespace KakeyaFormal.SpatialTubeLengths
open EuclideanSplit SpatialAngular SpatialTubeCover
noncomputable section

def coverWidth (width upperLength : ℝ) : ℝ := width+3*max 1 upperLength

theorem coverWidth_nonneg {width upperLength : ℝ} (hw : 0 ≤ width) :
    0 ≤ coverWidth width upperLength := by
  have hh := le_max_left (1:ℝ) upperLength
  unfold coverWidth
  linarith

/-- A cap-local finite axis of any length below the fixed upper bound lies in
the same label's finite parallel box, at a fixed enlarged cover width. -/
theorem length_in_box {k : ℕ} (u : Space (k+1)) (hu : ‖u‖ = 1)
    (T : UnitTube (k+1)) {δ tau width length upperLength : ℝ}
    (htau : 0 < tau) (hdr : δ ≤ tau) (hδ1 : δ ≤ 1) (hw : 0 ≤ width)
    (hL : length ≤ upperLength)
    (hcap : projectiveDistance T.direction u ≤ 3*tau) :
    SamplingGeometry.lengthCarrier T length (width*δ) ⊆
      SpatialTubeCover.parallelBox u tau (SpatialTubeCover.label u tau T)
        (2+coverWidth width upperLength) ((k:ℝ)+coverWidth width upperLength+3) := by
  rintro x ⟨t,ht,hxt⟩
  let U := max 1 upperLength
  have hU : 1 ≤ U := le_max_left _ _
  have htU : t ≤ U := ht.2.trans (hL.trans (le_max_right _ _))
  have hbase : dist x T.base ≤ U+width := by
    have he : dist (T.axisPoint t) T.base = t := by
      rw [dist_eq_norm,UnitTube.axisPoint,add_sub_cancel_left,norm_smul,
        Real.norm_eq_abs,T.unit_direction,mul_one,abs_of_nonneg ht.1]
    have hh := dist_triangle x (T.axisPoint t) T.base
    rw [he] at hh
    have hwδ := mul_le_mul_of_nonneg_left hδ1 hw
    linarith
  refine ⟨?_,?_⟩
  · have hp := (longitudinal_distance u x T.base).trans hbase
    have hq := GridCells.cell_center_distance
      (GridCells.gridCell_covers (by norm_num : (0:ℝ)<1) (longitudinal u T.base))
    norm_num only [Nat.cast_one,one_mul] at hq
    have hh := dist_triangle (longitudinal u x) (longitudinal u T.base)
      (cellCenter 1 (SpatialTubeCover.label u tau T).1)
    change dist (longitudinal u T.base) (cellCenter 1 (SpatialTubeCover.label u tau T).1) ≤ (1:ℝ)/2 at hq
    change dist (longitudinal u x) (cellCenter 1 (SpatialTubeCover.label u tau T).1) ≤
      2+(width+3*U)
    linarith
  · have hterr : ‖transverse u (x-T.axisPoint t)‖ ≤ width*δ :=
      (transverse_norm_le _ _).trans hxt
    have htdir : ‖transverse u T.direction‖ ≤ 3*tau := (transverse_direction_le u _ hu).trans hcap
    have hscalar : ‖t • transverse u T.direction‖ ≤ 3*U*tau := by
      rw [norm_smul,Real.norm_eq_abs,abs_of_nonneg ht.1]
      have hh := mul_le_mul_of_nonneg_left htdir ht.1
      have hb := mul_le_mul_of_nonneg_right htU (by positivity : 0 ≤ 3*tau)
      nlinarith
    have heq : transverse u x-transverse u T.base =
        transverse u (x-T.axisPoint t)+t • transverse u T.direction := by
      rw [transverse_sub,UnitTube.axisPoint,transverse_add,transverse_smul]
      abel
    have hnear : dist (transverse u x) (transverse u T.base) ≤ (width+3*U)*tau := by
      rw [dist_eq_norm,heq]
      have hh := norm_add_le (transverse u (x-T.axisPoint t)) (t • transverse u T.direction)
      nlinarith [mul_le_mul_of_nonneg_left hdr hw]
    have hq := GridCells.cell_center_distance (GridCells.gridCell_covers
      (by positivity : 0 < 2*tau) (transverse u T.base))
    have hh := dist_triangle (transverse u x) (transverse u T.base)
      (cellCenter (2*tau) (SpatialTubeCover.label u tau T).2)
    change dist (transverse u T.base) (cellCenter (2*tau) (SpatialTubeCover.label u tau T).2) ≤ (k:ℝ)*(2*tau)/2 at hq
    change dist (transverse u x) (cellCenter (2*tau) (SpatialTubeCover.label u tau T).2) ≤
      ((k:ℝ)+(width+3*U)+3)*tau
    nlinarith

end
end KakeyaFormal.SpatialTubeLengths
