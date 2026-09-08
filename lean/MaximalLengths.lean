import LengthTubeVolume
import MainMaximal

/-! Actual maximal-shading estimates for variable axis lengths and physical
widths in a fixed normalization. The original variable tube volumes remain
in both the shading-density hypotheses and the final sum. -/
namespace KakeyaFormal.MaximalLengths
open MeasureTheory Set SamplingGeometry WidthNormalization
open scoped BigOperators ENNReal
noncomputable section

def lowerScale (lengthLower width : ℝ) : ℝ := min 1 (min lengthLower width)
def upperScale (lengthUpper width : ℝ) : ℝ := max 1 (max lengthUpper width)
def densityFactor (n : ℕ) (lengthLower lengthUpper width : ℝ) : ℝ :=
  (lowerScale lengthLower width/upperScale lengthUpper width)^n

theorem scale_bounds {lengthLower lengthUpper width : ℝ}
    (hL : 0 < lengthLower) (hw : 0 < width) :
    0 < lowerScale lengthLower width ∧ lowerScale lengthLower width ≤ 1 ∧
    lowerScale lengthLower width ≤ lengthLower ∧ lowerScale lengthLower width ≤ width ∧
    1 ≤ upperScale lengthUpper width ∧ lengthUpper ≤ upperScale lengthUpper width ∧
    width ≤ upperScale lengthUpper width := by
  unfold lowerScale upperScale
  exact ⟨by positivity,min_le_left _ _,(min_le_right _ _).trans (min_le_left _ _),
    (min_le_right _ _).trans (min_le_right _ _),le_max_left _ _,
    (le_max_left _ _).trans (le_max_right _ _),(le_max_right _ _).trans (le_max_right _ _)⟩

theorem densityFactor_bounds (n : ℕ) {lengthLower lengthUpper width : ℝ}
    (hL : 0 < lengthLower) (hw : 0 < width) :
    0 < densityFactor n lengthLower lengthUpper width ∧
      densityFactor n lengthLower lengthUpper width ≤ 1 := by
  obtain ⟨hs,hs1,_,_,hW,_,_⟩ := scale_bounds (lengthUpper:=lengthUpper) hL hw
  have hWp : 0 < upperScale lengthUpper width := zero_lt_one.trans_le hW
  unfold densityFactor
  exact ⟨pow_pos (div_pos hs hWp) _,pow_le_one₀ (div_nonneg hs.le hWp.le)
    ((div_le_one hWp).mpr (hs1.trans hW))⟩

def family {n M : ℕ} (F : TubeFamily n M) (W : ℝ) : TubeFamily n M where
  tube i := normalizedTube (F.tube i) W
  shade := F.shade

/-- The original position-unrestricted unit-tube theorem implies the actual
variable-length and fixed-width conclusion. All geometric constants, including
both length bounds, are chosen before the original scale, data and tube volumes.
No bounded-position, cap, two-ends or volume-comparison premise is supplied. -/
theorem from_estimate {k : ℕ} {d : ℝ} (h : MaximalShading.Estimate (k+1) d)
    (lengthLower lengthUpper width separation : ℝ)
    (hL : 0 < lengthLower) (hw : 0 < width) (hsep : 0 < separation)
    (eps : ℝ) (heps : 0 < eps) :
    ∃ c : ℝ, 0 < c ∧ ∀ {M : ℕ} (F : TubeFamily (k+1) M)
      (lengths : Fin M → ℝ) (Y : Fin M → Set (Space (k+1))) {δ lam : ℝ},
      0 < δ → δ ≤ 1 → 0 < lam → lam ≤ 1 →
      (∀ i, lengthLower ≤ lengths i ∧ lengths i ≤ lengthUpper) →
      (∀ i, MeasurableSet (Y i)) →
      (∀ i, Y i ⊆ lengthCarrier (F.tube i) (lengths i) (width*δ)) →
      (∀ i, lam*(volume : Measure (Space (k+1))).real
        (lengthCarrier (F.tube i) (lengths i) (width*δ)) ≤ volume.real (Y i)) →
      F.Separated (separation*δ) →
      c*δ^((k+1:ℕ)-d+eps)*lam^d*
        (∑ i, (volume : Measure (Space (k+1))).real
          (lengthCarrier (F.tube i) (lengths i) (width*δ))) ≤
        volume.real (⋃ i,Y i) := by
  obtain ⟨hs,hs1,hsL,hsw,hW,hLW,hwW⟩ := scale_bounds (lengthUpper:=lengthUpper) hL hw
  have hWp : 0 < upperScale lengthUpper width := zero_lt_one.trans_le hW
  obtain ⟨hr,hr1⟩ := densityFactor_bounds (k+1) (lengthUpper:=lengthUpper) hL hw
  obtain ⟨c,hc,hmain⟩ := h separation hsep eps heps
  let s := lowerScale lengthLower width
  let W := upperScale lengthUpper width
  let r := densityFactor (k+1) lengthLower lengthUpper width
  refine ⟨c*r^d,by positivity,?_⟩
  intro M F lengths Y δ lam hδ hδ1 hlam hlam1 hlength hY hsub hmass hdir
  have hnlam : 0 < lam*r := mul_pos hlam hr
  have hnlam1 : lam*r ≤ 1 := by nlinarith [mul_nonneg hlam.le (sub_nonneg.mpr hr1)]
  have hrid : r=s^(k+1)/W^(k+1) := by dsimp [r,densityFactor,s,W]; rw [div_pow]
  have hnormsub (i : Fin M) : normalizedSet W (Y i) ⊆ ((family F W).tube i).carrier δ :=
    (Set.image_mono (hsub i)).trans
      (LengthTubeVolume.containing_unit_carrier (F.tube i) hWp ((hlength i).2.trans hLW) hwW hδ.le)
  have hnormmass (i : Fin M) :
      (lam*r)*(volume : Measure (Space (k+1))).real (((family F W).tube i).carrier δ) ≤
        volume.real (normalizedSet W (Y i)) := by
    have hlo := LengthTubeVolume.volume_lower (F.tube i) hs (hsL.trans (hlength i).1) hsw hδ.le
    calc
      _ = (lam*(s^(k+1)*volume.real ((F.tube i).carrier δ)))/W^(k+1) := by
        rw [TubeIsometryVolume.carrier_real_volume_eq ((family F W).tube i) (F.tube i) δ,hrid]
        ring
      _ ≤ (lam*volume.real (lengthCarrier (F.tube i) (lengths i) (width*δ)))/W^(k+1) :=
        div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_left hlo hlam.le) (pow_pos hWp _).le
      _ ≤ volume.real (Y i)/W^(k+1) := div_le_div_of_nonneg_right (hmass i) (pow_pos hWp _).le
      _ = _ := (normalized_volume hWp (Y i)).symm
  have hnsep : (family F W).Separated (separation*δ) := hdir
  have hbound := hmain (family F W) (fun i => normalizedSet W (Y i)) hδ hδ1 hnlam hnlam1
    (fun i => normalized_measurable hWp (hY i)) hnormsub hnormmass hnsep
  rw [normalized_union_volume hWp] at hbound
  have hsum : (∑ i, (volume : Measure (Space (k+1))).real
      (lengthCarrier (F.tube i) (lengths i) (width*δ))) ≤
      W^(k+1)*∑ i, volume.real (((family F W).tube i).carrier δ) := by
    rw [Finset.mul_sum]
    apply Finset.sum_le_sum
    intro i _
    rw [TubeIsometryVolume.carrier_real_volume_eq ((family F W).tube i) (F.tube i) δ]
    exact LengthTubeVolume.volume_upper (F.tube i) hWp ((hlength i).2.trans hLW) hwW hδ.le
  have hscaled := mul_le_mul_of_nonneg_left hsum
    (by positivity : 0 ≤ c*δ^((k+1:ℕ)-d+eps)*(lam*r)^d)
  have hbound' := (le_div_iff₀ (pow_pos hWp (k+1))).mp hbound
  have hcombined := hscaled.trans (by simpa only [mul_assoc,mul_comm,mul_left_comm] using hbound')
  rw [Real.mul_rpow hlam.le hr.le] at hcombined
  simpa only [mul_assoc,mul_comm,mul_left_comm] using hcombined

/-- The full fixed-length convention, with actual original variable tube
volumes and arbitrary positions. No estimate or geometric conclusion is
encoded as a field of the input data. -/
def Estimate (n : ℕ) (d : ℝ) : Prop :=
  ∀ lengthLower lengthUpper width separation : ℝ,
    0 < lengthLower → 0 < width → 0 < separation →
    ∀ eps : ℝ, 0 < eps → ∃ c : ℝ, 0 < c ∧
      ∀ {M : ℕ} (F : TubeFamily n M) (lengths : Fin M → ℝ)
        (Y : Fin M → Set (Space n)) {δ lam : ℝ},
      0 < δ → δ ≤ 1 → 0 < lam → lam ≤ 1 →
      (∀ i, lengthLower ≤ lengths i ∧ lengths i ≤ lengthUpper) →
      (∀ i, MeasurableSet (Y i)) →
      (∀ i, Y i ⊆ lengthCarrier (F.tube i) (lengths i) (width*δ)) →
      (∀ i, lam*(volume : Measure (Space n)).real
        (lengthCarrier (F.tube i) (lengths i) (width*δ)) ≤ volume.real (Y i)) →
      F.Separated (separation*δ) →
      c*δ^((n:ℝ)-d+eps)*lam^d*
        (∑ i, (volume : Measure (Space n)).real
          (lengthCarrier (F.tube i) (lengths i) (width*δ))) ≤
        volume.real (⋃ i,Y i)

theorem of_unit {k : ℕ} {d : ℝ} (h : MaximalShading.Estimate (k+1) d) :
    Estimate (k+1) d := by
  intro l u w s hl hw hs eps heps
  exact from_estimate h l u w s hl hw hs eps heps

/-- The actual main conclusion for every integer ambient dimension at least
six, with the blanket fixed length/width convention now included. -/
theorem endpoint {n : ℕ} (hn : 6 ≤ n) :
    Estimate n (KakeyaScalar.limitProfile ((n:ℝ)-1)) := by
  cases n with
  | zero => omega
  | succ k => exact of_unit (MainMaximal.endpoint hn)

theorem endpoint_formula {n : ℕ} (hn : 6 ≤ n) :
    Estimate n (3+(2-Real.sqrt 2)*((n:ℝ)-4)) := by
  cases n with
  | zero => omega
  | succ k => exact of_unit (MainMaximal.endpoint_formula hn)

theorem six_first : Estimate 6 (33/8) := of_unit MainMaximal.six_first
theorem six_endpoint : Estimate 6 (7-2*Real.sqrt 2) := of_unit MainMaximal.six_endpoint
theorem eight_endpoint : Estimate 8 (11-4*Real.sqrt 2) := of_unit MainMaximal.eight_endpoint
theorem six_diagonal_limit : Estimate 6 (29/7) := of_unit MainMaximal.six_diagonal_limit
theorem eight_diagonal_limit : Estimate 8 (37/7) := of_unit MainMaximal.eight_diagonal_limit

end
end KakeyaFormal.MaximalLengths
