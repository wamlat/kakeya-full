import KakeyaOperator
import ProjectiveGeometry

/-! Actual upper sphere-cap measure from the radial cone and a literal unit
tube. The sphere measure is the polar-coordinate measure supplied by Mathlib.
Finite covered sets need not be measurable for the outer-measure bound. -/
namespace KakeyaFormal.SphereCapMeasure
open MeasureTheory Finset KakeyaOperator
open scoped Pointwise ENNReal
noncomputable section
open Classical

def chordCap {n : ℕ} (v : Space n) (r : ℝ) : Set (Direction n) :=
  {w | dist (w:Space n) v ≤ r}

def projectiveCap {n : ℕ} (v : Space n) (r : ℝ) : Set (Direction n) :=
  {w | projectiveDistance (w:Space n) v ≤ r}

def radialCone {n : ℕ} (S : Set (Direction n)) : Set (Space n) :=
  Set.Ioo (0:ℝ) 1 • (Subtype.val '' S)

def tubeUpperConstant (n : ℕ) : ℝ := 3*(2:ℝ)^n*TubeVolume.unitBallVolume n
def capConstant (n : ℕ) : ℝ := 2*(n:ℝ)*tubeUpperConstant n

theorem sphere_finite {n : ℕ} (S : Set (Direction n)) : (sphereMeasure n) S ≠ ∞ := by
  change (volume : Measure (Space n)).toSphere S ≠ ∞
  exact measure_ne_top _ _

theorem tubeUpperConstant_pos (n : ℕ) : 0 < tubeUpperConstant n := by
  have h := TubeVolume.unitBallVolume_pos n
  unfold tubeUpperConstant
  positivity

theorem capConstant_pos {n : ℕ} (hn : 0 < n) : 0 < capConstant n := by
  have h := tubeUpperConstant_pos n
  have hn' : (0:ℝ) < n := Nat.cast_pos.mpr hn
  unfold capConstant
  positivity

theorem chordCap_measurable {n : ℕ} (v : Space n) (r : ℝ) : MeasurableSet (chordCap v r) :=
  (isClosed_le (continuous_subtype_val.dist continuous_const) continuous_const).measurableSet

theorem projective_continuous {n : ℕ} (v : Space n) :
    Continuous (fun w : Direction n => projectiveDistance (w:Space n) v) :=
  ((continuous_subtype_val.sub continuous_const).norm).min
    ((continuous_subtype_val.add continuous_const).norm)

theorem projectiveCap_measurable {n : ℕ} (v : Space n) (r : ℝ) : MeasurableSet (projectiveCap v r) :=
  (isClosed_le (projective_continuous v) continuous_const).measurableSet

/-- The cone over an oriented chord cap lies in the actual unit tube with
the cap center as its direction and the origin as its base. -/
theorem cone_subset_tube {n : ℕ} (v : Direction n) {r : ℝ} (hr : 0 ≤ r) :
    radialCone (chordCap (v:Space n) r) ⊆ (KakeyaOperator.tube v 0).carrier r := by
  rintro x ⟨t,ht,y,hy,rfl⟩
  obtain ⟨w,hw,rfl⟩ := hy
  refine ⟨t,⟨ht.1.le,ht.2.le⟩,?_⟩
  change dist (t • (w:Space n)) (0+t • (v:Space n)) ≤ r
  rw [zero_add,dist_smul₀,Real.norm_eq_abs,abs_of_pos ht.1]
  have hd : dist (w:Space n) (v:Space n) ≤ r := hw
  exact (mul_le_mul_of_nonneg_left hd ht.1.le).trans (mul_le_of_le_one_left hr ht.2.le)

/-- The actual polar sphere measure equals dimension times cone volume. -/
theorem sphere_cone_volume {n : ℕ} (S : Set (Direction n)) (hS : MeasurableSet S) :
    (sphereMeasure n).real S = (n:ℝ)*(volume : Measure (Space n)).real (radialCone S) := by
  have h := congrArg ENNReal.toReal ((volume : Measure (Space n)).toSphere_apply' hS)
  simpa only [sphereMeasure,Measure.real,radialCone,ENNReal.toReal_mul,
    finrank_euclideanSpace,Fintype.card_fin,ENNReal.toReal_natCast] using h

theorem scale_power {n : ℕ} {r : ℝ} (hr : 0 < r) :
    r^n/r = r^((n:ℝ)-1) := by
  rw [Real.rpow_sub hr,Real.rpow_natCast,Real.rpow_one]

/-- Oriented spherical caps have the required codimension-one upper measure;
the bound comes from the proved volume of their containing actual tube. -/
theorem chord_cap_upper {n : ℕ} (v : Direction n) {r : ℝ} (hr : 0 < r) (hr1 : r ≤ 1) :
    (sphereMeasure n).real (chordCap (v:Space n) r) ≤
      (n:ℝ)*tubeUpperConstant n*r^((n:ℝ)-1) := by
  rw [sphere_cone_volume _ (chordCap_measurable _ _)]
  have hcone := measureReal_mono (cone_subset_tube v hr.le) (TubeVolume.carrier_finite _ r)
  have htube := TubeVolume.carrier_volume_upper (KakeyaOperator.tube v 0) hr hr1
  have hh := mul_le_mul_of_nonneg_left (hcone.trans htube) (Nat.cast_nonneg (α:=ℝ) n)
  calc
    _ ≤ (n:ℝ)*(tubeUpperConstant n*r^n/r) := hh
    _ = _ := by rw [mul_div_assoc,scale_power hr]; ring

theorem projectiveCap_subset {n : ℕ} (v : Space n) (r : ℝ) :
    projectiveCap v r ⊆ chordCap v r ∪ chordCap (-v) r := by
  intro w hw
  change min ‖(w:Space n)-v‖ ‖(w:Space n)+v‖ ≤ r at hw
  rcases min_le_iff.mp hw with h | h
  · exact Or.inl (by simpa only [chordCap,Set.mem_ofPred_eq,dist_eq_norm] using h)
  · exact Or.inr (by simpa only [chordCap,Set.mem_ofPred_eq,dist_eq_norm,sub_neg_eq_add] using h)

/-- A projective cap is covered by the two oriented antipodal caps. -/
theorem projective_cap_upper {n : ℕ} (v : Direction n) {r : ℝ} (hr : 0 < r) (hr1 : r ≤ 1) :
    (sphereMeasure n).real (projectiveCap (v:Space n) r) ≤
      capConstant n*r^((n:ℝ)-1) := by
  let negv : Direction n := ⟨-(v:Space n),by
    simpa only [Metric.mem_sphere,dist_zero_right,norm_neg] using v.property⟩
  have h1 := chord_cap_upper v hr hr1
  have h2 := chord_cap_upper negv hr hr1
  have hmono := measureReal_mono (μ:=sphereMeasure n) (projectiveCap_subset (v:Space n) r) (sphere_finite _)
  have hunion := measureReal_union_le (μ:=sphereMeasure n) (chordCap (v:Space n) r) (chordCap (-(v:Space n)) r)
  have hh := hmono.trans hunion
  change (sphereMeasure n).real (chordCap (-(v:Space n)) r) ≤ _ at h2
  dsimp only [capConstant]
  linarith

/-- Finite projective-cap covers control actual sphere outer measure.
The covered set is arbitrary; no measurability or measure bound is assumed. -/
theorem finite_cover_upper {n : ℕ} {ι : Type*} (indices : Finset ι)
    (center : ι → Direction n) (S : Set (Direction n)) {r : ℝ}
    (hr : 0 < r) (hr1 : r ≤ 1)
    (hcover : ∀ v ∈ S, ∃ i ∈ indices, projectiveDistance (v:Space n) (center i:Space n) ≤ r) :
    (sphereMeasure n).real S ≤ capConstant n*r^((n:ℝ)-1)*(indices.card:ℝ) := by
  have hsub : S ⊆ ⋃ i ∈ indices, projectiveCap (center i:Space n) r := by
    intro v hv
    obtain ⟨i,hi,hv⟩ := hcover v hv
    exact Set.mem_iUnion₂.mpr ⟨i,hi,hv⟩
  have hmono := measureReal_mono (μ:=sphereMeasure n) hsub (sphere_finite _)
  have hunion := measureReal_biUnion_finset_le (μ:=sphereMeasure n) indices
    (fun i => projectiveCap (center i:Space n) r)
  have hs := sum_le_sum (s:=indices) (fun i _ => projective_cap_upper (center i) hr hr1)
  have hh := (hmono.trans hunion).trans hs
  simpa only [sum_const,nsmul_eq_mul,mul_comm] using hh

theorem indexed_cover_upper {n M : ℕ} (center : Fin M → Direction n) (S : Set (Direction n))
    {r : ℝ} (hr : 0 < r) (hr1 : r ≤ 1)
    (hcover : ∀ v ∈ S, ∃ i, projectiveDistance (v:Space n) (center i:Space n) ≤ r) :
    (sphereMeasure n).real S ≤ capConstant n*r^((n:ℝ)-1)*(M:ℝ) := by
  have hh := finite_cover_upper univ center S hr hr1 (fun v hv => by
    obtain ⟨i,hi⟩ := hcover v hv
    exact ⟨i,mem_univ _,hi⟩)
  simpa only [card_univ,Fintype.card_fin] using hh

/-- Extended-real version for direct use in a restricted weak level-set
inequality. Sphere outer measure is finite for every set. -/
theorem indexed_cover_upper_ennreal {n M : ℕ} (center : Fin M → Direction n) (S : Set (Direction n))
    {r : ℝ} (hr : 0 < r) (hr1 : r ≤ 1)
    (hcover : ∀ v ∈ S, ∃ i, projectiveDistance (v:Space n) (center i:Space n) ≤ r) :
    (sphereMeasure n) S ≤ ENNReal.ofReal (capConstant n*r^((n:ℝ)-1)*(M:ℝ)) := by
  have hh := ENNReal.ofReal_le_ofReal (indexed_cover_upper center S hr hr1 hcover)
  change ENNReal.ofReal (((sphereMeasure n) S).toReal) ≤ _ at hh
  rwa [ENNReal.ofReal_toReal (sphere_finite S)] at hh

end
end KakeyaFormal.SphereCapMeasure
