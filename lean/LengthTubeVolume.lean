import SamplingGeometry
import MeasurableSeedLengths
import TubeIsometryVolume

/-! Actual fixed-length/width volume normalization. The lower and upper
comparisons come from contained and containing homothetic unit carriers;
no formula for variable-length tube volume is assumed. -/
namespace KakeyaFormal.LengthTubeVolume
open MeasureTheory Set SamplingGeometry WidthNormalization Rescaling
open scoped ENNReal
noncomputable section

theorem carrier_compact {n : ℕ} (T : UnitTube n) (length radius : ℝ) :
    IsCompact (lengthCarrier T length radius) := by
  have heq : lengthCarrier T length radius =
      (fun p : ℝ × Space n => T.axisPoint p.1+p.2) ''
        (Set.Icc 0 length ×ˢ Metric.closedBall 0 radius) := by
    ext x
    constructor
    · rintro ⟨t,ht,hx⟩
      refine ⟨(t,x-T.axisPoint t),⟨ht,?_⟩,by simp⟩
      simpa only [Metric.mem_closedBall,dist_zero_right,dist_eq_norm,sub_zero] using hx
    · rintro ⟨⟨t,e⟩,⟨ht,he⟩,rfl⟩
      refine ⟨t,ht,?_⟩
      simpa only [Metric.mem_closedBall,dist_zero_right,dist_eq_norm,
        add_sub_cancel_left,sub_zero] using he
  rw [heq]
  apply (isCompact_Icc.prod (isCompact_closedBall (0:Space n) radius)).image
  unfold UnitTube.axisPoint
  fun_prop

theorem carrier_measurable {n : ℕ} (T : UnitTube n) (length radius : ℝ) :
    MeasurableSet (lengthCarrier T length radius) :=
  (carrier_compact T length radius).isClosed.measurableSet

theorem carrier_finite {n : ℕ} (T : UnitTube n) (length radius : ℝ) :
    (volume : Measure (Space n)) (lengthCarrier T length radius) ≠ ∞ :=
  (carrier_compact T length radius).measure_lt_top.ne

/-- A genuinely contained small homothetic unit tube, with the same original
base and direction after dilation. -/
theorem contained_unit_carrier {n : ℕ} (T : UnitTube n)
    {s length width δ : ℝ} (hs : 0 < s) (hsL : s ≤ length)
    (hsw : s ≤ width) (hδ : 0 ≤ δ) :
    normalizedSet (1/s) ((normalizedTube T s).carrier δ) ⊆
      lengthCarrier T length (width*δ) := by
  rintro x ⟨y,hy,rfl⟩
  obtain ⟨t,ht,hd⟩ := hy
  have ha : rescale (1/s) (0:Space n) ((normalizedTube T s).axisPoint t) =
      T.axisPoint (s*t) := by
    simp [normalizedTube,Rescaling.tube,UnitTube.axisPoint,rescale,
      smul_add,smul_smul,hs.ne']
  refine ⟨s*t,⟨mul_nonneg hs.le ht.1,?_⟩,?_⟩
  · exact (mul_le_mul_of_nonneg_left ht.2 hs.le).trans (by simpa using hsL)
  · rw [← ha,rescale_distance (one_div_pos.mpr hs)]
    have hh := div_le_div_of_nonneg_right hd (one_div_pos.mpr hs).le
    have he : δ/(1/s)=s*δ := by field_simp
    rw [he] at hh
    exact hh.trans (mul_le_mul_of_nonneg_right hsw hδ)

/-- A single common dilation contains every original bounded-length carrier
in an actual unit carrier at the same final radius delta. -/
theorem containing_unit_carrier {n : ℕ} (T : UnitTube n)
    {W length width δ : ℝ} (hW : 0 < W) (hLW : length ≤ W)
    (hwW : width ≤ W) (hδ : 0 ≤ δ) :
    normalizedSet W (lengthCarrier T length (width*δ)) ⊆
      (normalizedTube T W).carrier δ := by
  intro x hx
  obtain ⟨t,ht,hd⟩ := normalized_length_carrier T hW hLW _ (Set.Subset.rfl) hx
  refine ⟨t,ht,hd.trans ?_⟩
  have hh : width*δ ≤ W*δ := mul_le_mul_of_nonneg_right hwW hδ
  have he : width*(δ/W) = (width*δ)/W := by ring
  rw [he]
  exact (div_le_iff₀ hW).mpr (by simpa only [mul_comm] using hh)

/-- Lower volume comparison obtained from the explicit contained set. -/
theorem volume_lower {k : ℕ} (T : UnitTube (k+1))
    {s length width δ : ℝ} (hs : 0 < s) (hsL : s ≤ length)
    (hsw : s ≤ width) (hδ : 0 ≤ δ) :
    s^(k+1)*(volume : Measure (Space (k+1))).real (T.carrier δ) ≤
      volume.real (lengthCarrier T length (width*δ)) := by
  have hh := measureReal_mono (contained_unit_carrier T hs hsL hsw hδ)
    (carrier_finite T length (width*δ))
  rw [normalized_volume (one_div_pos.mpr hs),
    TubeIsometryVolume.carrier_real_volume_eq (normalizedTube T s) T δ] at hh
  simpa only [one_div,inv_pow,div_inv_eq_mul,mul_comm] using hh

/-- Upper volume comparison obtained from the common containing carrier. -/
theorem volume_upper {k : ℕ} (T : UnitTube (k+1))
    {W length width δ : ℝ} (hW : 0 < W) (hLW : length ≤ W)
    (hwW : width ≤ W) (hδ : 0 ≤ δ) :
    (volume : Measure (Space (k+1))).real (lengthCarrier T length (width*δ)) ≤
      W^(k+1)*volume.real (T.carrier δ) := by
  have hh := measureReal_mono (containing_unit_carrier T hW hLW hwW hδ)
    (TubeVolume.carrier_finite (normalizedTube T W) δ)
  rw [normalized_volume hW,
    TubeIsometryVolume.carrier_real_volume_eq (normalizedTube T W) T δ] at hh
  exact ((div_le_iff₀ (pow_pos hW (k+1))).mp hh).trans_eq (by ring)

end
end KakeyaFormal.LengthTubeVolume
