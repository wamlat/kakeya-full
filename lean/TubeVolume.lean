import GridGeometry

/-! Actual Euclidean tube carrier measurability and volume estimates. The
upper bound uses a finite axis mesh; the lower bound uses disjoint interior balls.
No analytic Kakeya estimate is assumed. -/
open MeasureTheory Set Metric
open scoped ENNReal
namespace KakeyaFormal.TubeVolume
open KakeyaFormal.GridGeometry

noncomputable def unitBallVolume (k : ℕ) : ℝ :=
  (volume : Measure (Space k)).real (Metric.closedBall 0 1)

theorem carrier_compact {k : ℕ} (T : UnitTube k) (δ : ℝ) :
    IsCompact (T.carrier δ) := by
  have heq : T.carrier δ =
      (fun p : ℝ × Space k => T.axisPoint p.1 + p.2) ''
        (Set.Icc 0 1 ×ˢ Metric.closedBall 0 δ) := by
    ext x
    constructor
    · rintro ⟨t,ht,hx⟩
      refine ⟨(t,x-T.axisPoint t),⟨ht,?_⟩,by simp⟩
      simpa only [Metric.mem_closedBall,dist_zero_right,dist_eq_norm,sub_zero] using hx
    · rintro ⟨⟨t,e⟩,⟨ht,he⟩,rfl⟩
      refine ⟨t,ht,?_⟩
      simpa only [Metric.mem_closedBall,dist_zero_right,dist_eq_norm,add_sub_cancel_left,sub_zero] using he
  rw [heq]
  apply (isCompact_Icc.prod (isCompact_closedBall (0 : Space k) δ)).image
  unfold UnitTube.axisPoint
  fun_prop

theorem carrier_measurable {k : ℕ} (T : UnitTube k) (δ : ℝ) :
    MeasurableSet (T.carrier δ) := (carrier_compact T δ).isClosed.measurableSet

theorem carrier_finite {k : ℕ} (T : UnitTube k) (δ : ℝ) :
    volume (T.carrier δ) ≠ ∞ := (carrier_compact T δ).measure_lt_top.ne

theorem ball_volume_scale {k : ℕ} (x : Space k) {r : ℝ} (hr : 0 ≤ r) :
    (volume : Measure (Space k)).real (Metric.closedBall x r) = r^k * unitBallVolume k := by
  simpa only [finrank_euclideanSpace,Fintype.card_fin,unitBallVolume] using
    Measure.addHaar_real_closedBall' (volume : Measure (Space k)) x hr

/-- Finite geometric cover of the whole tube, including endpoint caps. -/
theorem carrier_mesh_cover {k : ℕ} (T : UnitTube k) {δ : ℝ} (hδ : 0 < δ) :
    T.carrier δ ⊆ ⋃ j ∈ Finset.range (Nat.ceil (1/δ)+1),
      Metric.closedBall (T.axisPoint ((j:ℝ)*δ)) (2*δ) := by
  rintro x ⟨t,ht,hxt⟩
  obtain ⟨j,hj,htj⟩ := unit_parameter_mesh hδ ht
  apply Set.mem_iUnion.mpr
  refine ⟨j,Set.mem_iUnion.mpr ⟨hj,?_⟩⟩
  have htri := dist_triangle x (T.axisPoint t) (T.axisPoint ((j:ℝ)*δ))
  rw [T.axisPoint_distance] at htri
  change dist x (T.axisPoint ((j:ℝ)*δ)) ≤ 2*δ
  linarith

/-- Explicit volume upper bound in the equivalent form C*δ^k/δ. -/
theorem carrier_volume_upper {k : ℕ} (T : UnitTube k) {δ : ℝ}
    (hδ : 0 < δ) (hδ1 : δ ≤ 1) :
    (volume : Measure (Space k)).real (T.carrier δ) ≤
      (3*(2:ℝ)^k*unitBallVolume k)*δ^k/δ := by
  let S := Finset.range (Nat.ceil (1/δ)+1)
  let B := fun j : ℕ => Metric.closedBall (T.axisPoint ((j:ℝ)*δ)) (2*δ)
  have hfinite : volume (⋃ j ∈ S, B j) ≠ ∞ :=
    measure_biUnion_ne_top S.finite_toSet (fun _ _ => measure_closedBall_lt_top.ne)
  have hm := measureReal_mono (carrier_mesh_cover T hδ) hfinite
  have hsum := measureReal_biUnion_finset_le (μ := (volume : Measure (Space k))) S B
  have hballs : ∑ j ∈ S, (volume : Measure (Space k)).real (B j) =
      ((Nat.ceil (1/δ):ℝ)+1)*(2*δ)^k*unitBallVolume k := by
    simp only [B,ball_volume_scale _ (by positivity : 0 ≤ 2*δ),Finset.sum_const,
      S,Finset.card_range,Nat.cast_add,Nat.cast_one,nsmul_eq_mul]
    ring
  rw [hballs] at hsum
  have hN : (1:ℝ) ≤ 1/δ := (le_div_iff₀ hδ).mpr (by simpa using hδ1)
  have hceil := Nat.ceil_lt_add_one (by positivity : 0 ≤ 1/δ)
  have hfactor : (Nat.ceil (1/δ):ℝ)+1 ≤ 3/δ := by
    have hid : 3/δ = 3*(1/δ) := by ring
    rw [hid]
    linarith
  have hv : 0 ≤ unitBallVolume k := measureReal_nonneg
  have hmul := mul_le_mul_of_nonneg_right hfactor
    (mul_nonneg (pow_nonneg (by positivity : 0 ≤ 2*δ) k) hv)
  have hlast : ((Nat.ceil (1/δ):ℝ)+1)*(2*δ)^k*unitBallVolume k ≤
      (3*(2:ℝ)^k*unitBallVolume k)*δ^k/δ := by
    simpa only [mul_pow,mul_assoc,mul_left_comm,mul_comm,div_eq_mul_inv] using hmul
  exact (hm.trans hsum).trans hlast

theorem unitBallVolume_pos (k : ℕ) : 0 < unitBallVolume k := by
  have hpos : 0 < (volume : Measure (Space k)) (Metric.closedBall 0 1) :=
    Metric.measure_closedBall_pos volume 0 (by norm_num)
  exact ENNReal.toReal_pos hpos.ne' measure_closedBall_lt_top.ne

/-- Interior balls at two-mesh spacing are genuinely pairwise disjoint. -/
theorem axis_balls_disjoint {k : ℕ} (T : UnitTube k) {δ : ℝ} (hδ : 0 < δ) :
    Pairwise (fun i j : ℕ => Disjoint
      (Metric.closedBall (T.axisPoint ((i:ℝ)*(2*δ))) (δ/2))
      (Metric.closedBall (T.axisPoint ((j:ℝ)*(2*δ))) (δ/2))) := by
  intro i j hij
  apply Metric.closedBall_disjoint_closedBall
  rw [T.axisPoint_distance]
  rcases lt_or_gt_of_ne hij with hlt | hgt
  · have hcast : (i:ℝ)+1 ≤ j := by exact_mod_cast hlt
    rw [abs_of_nonpos (by nlinarith : (i:ℝ)*(2*δ)-(j:ℝ)*(2*δ) ≤ 0)]
    nlinarith
  · have hcast : (j:ℝ)+1 ≤ i := by exact_mod_cast hgt
    rw [abs_of_nonneg (by nlinarith : 0 ≤ (i:ℝ)*(2*δ)-(j:ℝ)*(2*δ))]
    nlinarith

theorem interior_ball_subset_carrier {k : ℕ} (T : UnitTube k) {δ : ℝ}
    (hδ : 0 < δ) {j : ℕ} (hj : j ∈ Finset.range (Nat.floor (1/(2*δ))+1)) :
    Metric.closedBall (T.axisPoint ((j:ℝ)*(2*δ))) (δ/2) ⊆ T.carrier δ := by
  have hjnat := Finset.mem_range_succ_iff.mp hj
  have hfloor := Nat.floor_le (by positivity : 0 ≤ 1/(2*δ))
  have hjreal : (j:ℝ) ≤ 1/(2*δ) := (by exact_mod_cast hjnat : (j:ℝ) ≤ Nat.floor (1/(2*δ))).trans hfloor
  have ht : (j:ℝ)*(2*δ) ≤ 1 := (le_div_iff₀ (by positivity : 0 < 2*δ)).mp hjreal
  intro x hx
  refine ⟨(j:ℝ)*(2*δ),⟨by positivity,ht⟩,?_⟩
  change dist x (T.axisPoint ((j:ℝ)*(2*δ))) ≤ δ/2 at hx
  linarith

/-- Explicit lower bound from actual disjoint balls inside the tube. -/
theorem carrier_volume_lower {k : ℕ} (T : UnitTube k) {δ : ℝ} (hδ : 0 < δ) :
    (unitBallVolume k / ((2:ℝ)^(k+1))) * δ^k/δ ≤
      (volume : Measure (Space k)).real (T.carrier δ) := by
  let S := Finset.range (Nat.floor (1/(2*δ))+1)
  let B := fun j : ℕ => Metric.closedBall (T.axisPoint ((j:ℝ)*(2*δ))) (δ/2)
  have hsub : (⋃ j ∈ S, B j) ⊆ T.carrier δ := by
    intro x hx
    obtain ⟨j,hj,hx⟩ := Set.mem_iUnion₂.mp hx
    exact interior_ball_subset_carrier T hδ hj hx
  have hm := measureReal_mono hsub (carrier_finite T δ)
  have hsum := measureReal_biUnion_finset (μ := (volume : Measure (Space k)))
    (s := S) (f := B) (fun _ _ _ _ h => axis_balls_disjoint T hδ h)
    (fun _ _ => measurableSet_closedBall)
    (fun _ _ => measure_closedBall_lt_top.ne)
  have hballs : ∑ j ∈ S, (volume : Measure (Space k)).real (B j) =
      ((Nat.floor (1/(2*δ)):ℝ)+1)*(δ/2)^k*unitBallVolume k := by
    simp only [B,ball_volume_scale _ (by positivity : 0 ≤ δ/2),Finset.sum_const,
      S,Finset.card_range,Nat.cast_add,Nat.cast_one,nsmul_eq_mul]
    ring
  rw [hsum,hballs] at hm
  have hfloor : 1/(2*δ) ≤ (Nat.floor (1/(2*δ)):ℝ)+1 := (Nat.lt_floor_add_one _).le
  have hmul := mul_le_mul_of_nonneg_right hfloor
    (mul_nonneg (pow_nonneg (by positivity : 0 ≤ δ/2) k) (unitBallVolume_pos k).le)
  have hfirst : (unitBallVolume k / ((2:ℝ)^(k+1))) * δ^k/δ ≤
      ((Nat.floor (1/(2*δ)):ℝ)+1)*(δ/2)^k*unitBallVolume k := by
    have hid : (unitBallVolume k / ((2:ℝ)^(k+1))) * δ^k/δ =
        (1/(2*δ))*((δ/2)^k*unitBallVolume k) := by
      rw [div_pow,pow_succ]
      field_simp
    rw [hid]
    simpa only [mul_assoc] using hmul
  exact hfirst.trans hm

/-- Uniform two-sided tube volume comparison, valid for every actual unit tube. -/
theorem carrier_volume_comparison (k : ℕ) :
    ∃ c C : ℝ, 0 < c ∧ 0 < C ∧
      ∀ T : UnitTube k, ∀ δ : ℝ, 0 < δ → δ ≤ 1 →
        c*δ^k/δ ≤ (volume : Measure (Space k)).real (T.carrier δ) ∧
        (volume : Measure (Space k)).real (T.carrier δ) ≤ C*δ^k/δ := by
  refine ⟨unitBallVolume k/(2:ℝ)^(k+1),3*(2:ℝ)^k*unitBallVolume k,
    by positivity [unitBallVolume_pos k],by positivity [unitBallVolume_pos k],?_⟩
  intro T δ hδ hδ1
  exact ⟨carrier_volume_lower T hδ,carrier_volume_upper T hδ hδ1⟩

end KakeyaFormal.TubeVolume
