import TubeVolume
import TubeLocalCount
import PivotDirections

/-! Actual two-tube geometry and measure estimates needed in the hairbrush.
The separation parameter refers to the concrete unoriented chord distance. -/
open MeasureTheory Set Metric
open scoped ENNReal
namespace KakeyaFormal.TubeIntersection
open KakeyaFormal.GridGeometry KakeyaFormal.TubeVolume KakeyaFormal.PivotDirections
open KakeyaFormal.ProjectiveGeometry

theorem unit_projective_le_two {k : ℕ} (v w : Space k)
    (hv : ‖v‖ = 1) (hw : ‖w‖ = 1) : projectiveDistance v w ≤ 2 := by
  have h := (min_le_left ‖v-w‖ ‖v+w‖).trans (norm_sub_le v w)
  simpa only [projectiveDistance,hv,hw,show (1:ℝ)+1=2 by norm_num] using h

/-- Two common physical points force a short intersection at a transverse angle. -/
theorem common_point_distance {k : ℕ} (T S : UnitTube k) {δ theta : ℝ}
    (hδ : 0 < δ) (htheta : 0 < theta)
    (hangle : theta ≤ projectiveDistance T.direction S.direction)
    {x y : Space k} (hxT : x ∈ T.carrier δ) (hyT : y ∈ T.carrier δ)
    (hxS : x ∈ S.carrier δ) (hyS : y ∈ S.carrier δ) :
    dist x y ≤ 16*δ/theta := by
  have htheta2 := hangle.trans (unit_projective_le_two _ _ T.unit_direction S.unit_direction)
  by_cases hfar : 4*δ ≤ dist x y
  · have hr : 0 < dist x y := by linarith
    obtain ⟨s,_,hs⟩ := hxT
    obtain ⟨t,_,ht⟩ := hyT
    obtain ⟨s',_,hs'⟩ := hxS
    obtain ⟨t',_,ht'⟩ := hyS
    have hT := distant_two_point_direction_bound x y T.base T.direction
      T.unit_direction hr (le_refl _) hfar hs ht
    have hS := distant_two_point_direction_bound x y S.base S.direction
      S.unit_direction hr (le_refl _) hfar hs' ht'
    have hSr : projectiveDistance (unitize (y-x)) S.direction ≤ 8*δ/dist x y := by
      rw [projective_symm]
      exact hS
    have htri := projective_triangle T.direction (unitize (y-x)) S.direction
    have hang : theta ≤ 16*δ/dist x y := by
      calc
        _ ≤ projectiveDistance T.direction S.direction := hangle
        _ ≤ _ := htri
        _ ≤ 8*δ/dist x y + 8*δ/dist x y := add_le_add hT hSr
        _ = _ := by ring
    have hm := (le_div_iff₀ hr).mp hang
    exact (le_div_iff₀ htheta).mpr (by nlinarith)
  · have hnear : dist x y ≤ 4*δ := (lt_of_not_ge hfar).le
    have hm := mul_le_mul hnear htheta2 htheta.le (by positivity : 0 ≤ 4*δ)
    exact (le_div_iff₀ htheta).mpr (by nlinarith)

/-- A set in the δ-neighborhood of any finite segment has the expected linear
length contribution to its volume, even when the endpoints coincide. -/
theorem segment_neighborhood_volume {k : ℕ} (a b : Space k) {δ : ℝ}
    (hδ : 0 < δ) (U : Set (Space k))
    (hinc : ∀ x ∈ U, ∃ p ∈ segment ℝ a b, dist x p ≤ δ) :
    (volume : Measure (Space k)).real U ≤
      ((Nat.ceil (dist a b/δ):ℝ)+1)*(2*δ)^k*unitBallVolume k := by
  let J := Finset.range (Nat.ceil (dist a b/δ)+1)
  let B := fun j : ℕ => Metric.closedBall
    (AffineMap.lineMap a b ((j:ℝ)*(δ/dist a b))) (2*δ)
  have hcover : U ⊆ ⋃ j ∈ J, B j := by
    intro x hx
    obtain ⟨p,hp,hxp⟩ := hinc x hx
    rw [segment_eq_image_lineMap] at hp
    obtain ⟨t,ht,rfl⟩ := hp
    obtain ⟨j,hj,htj⟩ := segment_parameter_mesh a b hδ ht
    refine Set.mem_iUnion₂.mpr ⟨j,hj,?_⟩
    change dist x (AffineMap.lineMap a b ((j:ℝ)*(δ/dist a b))) ≤ 2*δ
    have htri := dist_triangle x (AffineMap.lineMap a b t)
      (AffineMap.lineMap a b ((j:ℝ)*(δ/dist a b)))
    linarith
  have hfinite : volume (⋃ j ∈ J, B j) ≠ ∞ :=
    measure_biUnion_ne_top J.finite_toSet (fun _ _ => measure_closedBall_lt_top.ne)
  have hm := measureReal_mono hcover hfinite
  have hsum := measureReal_biUnion_finset_le (μ := (volume : Measure (Space k))) J B
  have hballs : ∑ j ∈ J, (volume : Measure (Space k)).real (B j) =
      ((Nat.ceil (dist a b/δ):ℝ)+1)*(2*δ)^k*unitBallVolume k := by
    simp only [B,ball_volume_scale _ (by positivity : 0 ≤ 2*δ),Finset.sum_const,
      J,Finset.card_range,Nat.cast_add,Nat.cast_one,nsmul_eq_mul]
    ring
  rw [hballs] at hsum
  exact hm.trans hsum

/-- Tube intersection is localized to a short actual segment on either axis. -/
theorem intersection_segment {k : ℕ} (T S : UnitTube k) {δ theta : ℝ}
    (hδ : 0 < δ) (htheta : 0 < theta)
    (hangle : theta ≤ projectiveDistance T.direction S.direction)
    (hne : (T.carrier δ ∩ S.carrier δ).Nonempty) :
    ∃ a b : Space k, dist a b ≤ 40*δ/theta ∧
      ∀ x ∈ T.carrier δ ∩ S.carrier δ,
        ∃ p ∈ segment ℝ a b, dist x p ≤ δ := by
  obtain ⟨x₀,hx₀T,hx₀S⟩ := hne
  obtain ⟨t₀,ht₀,hx₀⟩ := hx₀T
  let R := 16*δ/theta+2*δ
  have hR : 0 < R := by dsimp [R]; positivity
  have ht0T : x₀ ∈ T.carrier δ := ⟨t₀,ht₀,hx₀⟩
  have htheta2 := hangle.trans (unit_projective_le_two _ _ T.unit_direction S.unit_direction)
  refine ⟨T.axisPoint (t₀-R),T.axisPoint (t₀+R),?_,?_⟩
  · rw [T.axisPoint_distance,abs_of_nonpos (by linarith : t₀-R-(t₀+R) ≤ 0)]
    dsimp [R]
    have hmul : 4*δ*theta ≤ 8*δ := by nlinarith
    have hlast := (le_div_iff₀ htheta).mpr hmul
    have hbound := add_le_add_left hlast (2*(16*δ/theta))
    convert hbound using 1 <;> first | rfl | ring
  · intro x hx
    have hxy := common_point_distance T S hδ htheta hangle hx.1 ht0T hx.2 hx₀S
    obtain ⟨t,_,hxt⟩ := hx.1
    have htri1 := dist_triangle (T.axisPoint t) x (T.axisPoint t₀)
    have htri2 := dist_triangle x x₀ (T.axisPoint t₀)
    have hxt' : dist (T.axisPoint t) x ≤ δ := by simpa only [dist_comm] using hxt
    rw [T.axisPoint_distance] at htri1
    have hgap : |t-t₀| ≤ R := by dsimp [R]; linarith
    obtain ⟨hlo,hhi⟩ := abs_le.mp hgap
    refine ⟨T.axisPoint t,TubeLocalCount.axisPoint_mem_segment T
      (by linarith) (by linarith) (by linarith),hxt⟩

/-- The sharp-in-angle elementary tube-intersection volume estimate. -/
theorem transverse_intersection_volume {k : ℕ} (T S : UnitTube k) {δ theta : ℝ}
    (hδ : 0 < δ) (htheta : 0 < theta)
    (hangle : theta ≤ projectiveDistance T.direction S.direction) :
    (volume : Measure (Space k)).real (T.carrier δ ∩ S.carrier δ) ≤
      (44*(2:ℝ)^k*unitBallVolume k)*δ^k/theta := by
  by_cases hne : (T.carrier δ ∩ S.carrier δ).Nonempty
  · obtain ⟨a,b,hab,hinc⟩ := intersection_segment T S hδ htheta hangle hne
    have hm := segment_neighborhood_volume a b hδ _ hinc
    have htheta2 := hangle.trans (unit_projective_le_two _ _ T.unit_direction S.unit_direction)
    have hd := div_le_div_of_nonneg_right hab hδ.le
    have hid : (40*δ/theta)/δ = 40/theta := by field_simp
    rw [hid] at hd
    have hc := Nat.ceil_lt_add_one (div_nonneg (dist_nonneg : 0 ≤ dist a b) hδ.le)
    have hfour : (2:ℝ) ≤ 4/theta := (le_div_iff₀ htheta).mpr (by linarith)
    have hfactor : (Nat.ceil (dist a b/δ):ℝ)+1 ≤ 44/theta := by
      calc
        _ ≤ dist a b/δ+2 := by linarith
        _ ≤ 40/theta+4/theta := add_le_add hd hfour
        _ = _ := by ring
    have hmul := mul_le_mul_of_nonneg_right hfactor
      (mul_nonneg (pow_nonneg (by positivity : 0 ≤ 2*δ) k) (unitBallVolume_pos k).le)
    have hlast : ((Nat.ceil (dist a b/δ):ℝ)+1)*(2*δ)^k*unitBallVolume k ≤
        (44*(2:ℝ)^k*unitBallVolume k)*δ^k/theta := by
      simpa only [mul_pow,mul_assoc,mul_left_comm,mul_comm,div_eq_mul_inv] using hmul
    exact hm.trans hlast
  · rw [Set.not_nonempty_iff_eq_empty.mp hne,measureReal_empty]
    have hv := unitBallVolume_pos k
    positivity

/-- Parallel and transverse pairs in one bound, including their endpoint caps. -/
theorem intersection_volume_upper {k : ℕ} (T S : UnitTube k) {δ : ℝ}
    (hδ : 0 < δ) (hδ1 : δ ≤ 1) :
    (volume : Measure (Space k)).real (T.carrier δ ∩ S.carrier δ) ≤
      (44*(2:ℝ)^k*unitBallVolume k)*δ^k /
        max (projectiveDistance T.direction S.direction) δ := by
  by_cases hangle : projectiveDistance T.direction S.direction ≤ δ
  · rw [max_eq_right hangle]
    have hm : (volume : Measure (Space k)).real (T.carrier δ ∩ S.carrier δ) ≤
        (volume : Measure (Space k)).real (T.carrier δ) :=
      measureReal_mono Set.inter_subset_left (carrier_finite T δ)
    have ht := carrier_volume_upper T hδ hδ1
    have hfactor : (3*(2:ℝ)^k*unitBallVolume k)*δ^k/δ ≤
        (44*(2:ℝ)^k*unitBallVolume k)*δ^k/δ := by
      have hv := unitBallVolume_pos k
      apply div_le_div_of_nonneg_right _ hδ.le
      have hnonneg : 0 ≤ (2:ℝ)^k*unitBallVolume k*δ^k := by positivity
      nlinarith
    exact (hm.trans ht).trans hfactor
  · have hd : δ < projectiveDistance T.direction S.direction := lt_of_not_ge hangle
    rw [max_eq_left hd.le]
    exact transverse_intersection_volume T S hδ (hδ.trans hd) le_rfl

end KakeyaFormal.TubeIntersection
