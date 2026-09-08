import MaximalLengths
import MeasurableToDiscrete

/-! The real-cap measurable shading estimate with actual bounded variable
axis lengths. The exact original tube-volume sum is preserved in the result;
one common spatial map supplies all normalization and volume comparisons. -/
namespace KakeyaFormal.MeasurableLengthEstimates
open MeasureTheory Set SamplingGeometry WidthNormalization MaximalLengths
open scoped BigOperators ENNReal
noncomputable section

/-- Source volume form (1.5), with a fixed physical length interval and width,
and the actual original variable-length tube volumes in both occurrences. -/
def Estimate (n : ℕ) (m d p : ℝ) : Prop :=
  ∀ geom : MeasurableNormalization, ∀ lengthLower lengthUpper width : ℝ,
    0 < lengthLower → 0 < width → ∀ eps : ℝ, 0 < eps →
    ∃ c : ℝ, 0 < c ∧ ∀ {M : ℕ} (F : TubeFamily n M)
      (lengths : Fin M → ℝ) (Y : Fin M → Set (Space n)) {δ lam A : ℝ},
      0 < δ → δ ≤ 1 → 0 < lam → lam ≤ 1 → 1 ≤ A →
      (∀ i, lengthLower ≤ lengths i ∧ lengths i ≤ lengthUpper) →
      (∀ i, MeasurableSet (Y i)) →
      (∀ i, Y i ⊆ lengthCarrier (F.tube i) (lengths i) (width*δ)) →
      (∀ i, lam*(volume : Measure (Space n)).real
        (lengthCarrier (F.tube i) (lengths i) (width*δ)) ≤ volume.real (Y i)) →
      F.Separated (geom.separation*δ) → F.Bounded geom.radius → F.CapBound δ m A →
      c*A⁻¹*δ^(m+1-d+eps)*lam^p*
        (∑ i, (volume : Measure (Space n)).real
          (lengthCarrier (F.tube i) (lengths i) (width*δ))) ≤ volume.real (⋃ i,Y i)

/-- The concrete unit-axis volume estimate supplies the complete wider-length
predicate. No volume comparison, changed cap, or normalized family is an input. -/
theorem of_volume {k : ℕ} {m d p : ℝ}
    (h : VolumeMeasurableEstimate (k+1) m d p) : Estimate (k+1) m d p := by
  intro geom l u width hl hw eps heps
  obtain ⟨hs,_,hsl,hsw,hW,hul,hwW⟩ := scale_bounds (lengthUpper:=u) hl hw
  have hWp : 0 < upperScale u width := zero_lt_one.trans_le hW
  obtain ⟨hr,hr1⟩ := densityFactor_bounds (k+1) (lengthUpper:=u) hl hw
  obtain ⟨c,hc,hmain⟩ := h geom eps heps
  let s := lowerScale l width
  let W := upperScale u width
  let r := densityFactor (k+1) l u width
  refine ⟨c*r^p,by positivity,?_⟩
  intro M F lengths Y δ lam A hδ hδ1 hlam hlam1 hA hlength hY hsub hmass hdir hbase hcap
  have hnlam : 0 < lam*r := mul_pos hlam hr
  have hnlam1 : lam*r ≤ 1 := by nlinarith [mul_nonneg hlam.le (sub_nonneg.mpr hr1)]
  have hrid : r=s^(k+1)/W^(k+1) := by dsimp [r,densityFactor,s,W]; rw [div_pow]
  have hnormsub (i : Fin M) : normalizedSet W (Y i) ⊆ ((MaximalLengths.family F W).tube i).carrier δ :=
    (Set.image_mono (hsub i)).trans
      (LengthTubeVolume.containing_unit_carrier (F.tube i) hWp ((hlength i).2.trans hul) hwW hδ.le)
  have hnormmass (i : Fin M) :
      (lam*r)*(volume : Measure (Space (k+1))).real (((MaximalLengths.family F W).tube i).carrier δ) ≤
        volume.real (normalizedSet W (Y i)) := by
    have hlo := LengthTubeVolume.volume_lower (F.tube i) hs (hsl.trans (hlength i).1) hsw hδ.le
    calc
      _ = (lam*(s^(k+1)*volume.real ((F.tube i).carrier δ)))/W^(k+1) := by
        rw [TubeIsometryVolume.carrier_real_volume_eq ((MaximalLengths.family F W).tube i) (F.tube i) δ,hrid]
        ring
      _ ≤ (lam*volume.real (lengthCarrier (F.tube i) (lengths i) (width*δ)))/W^(k+1) :=
        div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_left hlo hlam.le) (pow_pos hWp _).le
      _ ≤ volume.real (Y i)/W^(k+1) := div_le_div_of_nonneg_right (hmass i) (pow_pos hWp _).le
      _ = _ := (normalized_volume hWp (Y i)).symm
  let H : MeasurableConfiguration (k+1) geom m := {
    M := M, δ := δ, lam := lam*r, A := A, family := MaximalLengths.family F W,
    shading := fun i => normalizedSet W (Y i),
    scale_pos := hδ, scale_le_one := hδ1, density_pos := hnlam, density_le_one := hnlam1,
    cap_ge_one := hA, shading_measurable := fun i => normalized_measurable hWp (hY i),
    shading_subset := hnormsub, shading_mass := hnormmass,
    separated := hdir, cap_bound := hcap,
    bounded := fun i => MeasurableToDiscrete.normalized_base_bound (F.tube i) hW
      geom.radius_pos.le (hbase i) }
  have hbound := hmain H
  change c*A⁻¹*δ^(m+1-d+eps)*(lam*r)^p*
    (∑ i, volume.real (((MaximalLengths.family F W).tube i).carrier δ)) ≤
      volume.real (⋃ i, normalizedSet W (Y i)) at hbound
  rw [normalized_union_volume hWp] at hbound
  have hsum : (∑ i, (volume : Measure (Space (k+1))).real
      (lengthCarrier (F.tube i) (lengths i) (width*δ))) ≤
      W^(k+1)*∑ i, volume.real (((MaximalLengths.family F W).tube i).carrier δ) := by
    rw [Finset.mul_sum]
    apply Finset.sum_le_sum
    intro i _
    rw [TubeIsometryVolume.carrier_real_volume_eq ((MaximalLengths.family F W).tube i) (F.tube i) δ]
    exact LengthTubeVolume.volume_upper (F.tube i) hWp ((hlength i).2.trans hul) hwW hδ.le
  have hAp : 0 < A := zero_lt_one.trans_le hA
  have hscaled := mul_le_mul_of_nonneg_left hsum
    (by positivity : 0 ≤ c*A⁻¹*δ^(m+1-d+eps)*(lam*r)^p)
  have hbound' := (le_div_iff₀ (pow_pos hWp (k+1))).mp hbound
  have hcombined := hscaled.trans (by simpa only [mul_assoc,mul_comm,mul_left_comm] using hbound')
  rw [Real.mul_rpow hlam.le hr.le] at hcombined
  simpa only [mul_assoc,mul_comm,mul_left_comm] using hcombined

/-- The actual real-cap endpoint, including the fixed-length normalization,
in every adequate positive integer ambient dimension. -/
theorem real_cap_endpoint {k : ℕ} {m : ℝ} (hm : 3 < m) (hdim : m ≤ (k:ℝ)) :
    Estimate (k+1) m (KakeyaScalar.limitProfile m) (max (KakeyaScalar.limitProfile m) 4) := by
  apply of_volume
  apply MeasurableEstimate.volume_form
  apply MainEndpoint.real_cap_measurable hm (k+1) (by omega)
  simpa only [Nat.cast_add,Nat.cast_one,add_sub_cancel_right] using hdim

theorem diagonal_endpoint {n : ℕ} (hn : 6 ≤ n) :
    Estimate n ((n:ℝ)-1) (KakeyaScalar.limitProfile ((n:ℝ)-1))
      (KakeyaScalar.limitProfile ((n:ℝ)-1)) := by
  cases n with
  | zero => omega
  | succ k => exact of_volume (MainEndpoint.diagonal_volume hn)

end
end KakeyaFormal.MeasurableLengthEstimates
