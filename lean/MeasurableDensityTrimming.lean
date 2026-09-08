import TubeVolume
import Mathlib.MeasureTheory.Integral.DominatedConvergence
import Mathlib.Topology.Order.IntermediateValue

/-! Exact-volume subsets of actual measurable Euclidean shadings. Radial cuts
use null sphere boundaries and the intermediate value theorem. No grid
approximation or assumed prescribed-mass selection theorem is used. -/
namespace KakeyaFormal.MeasurableDensityTrimming
open MeasureTheory Set Metric Filter
open scoped ENNReal Topology BigOperators
noncomputable section
open Classical

/-- The radial distribution of restricted Euclidean volume has no point masses:
a fiber is an actual Euclidean sphere, whose Lebesgue volume is zero. -/
theorem radial_no_atoms {n : ℕ} (Y : Set (Space (n+1))) :
    NullSingletonClass ((volume.restrict Y).map (fun x : Space (n+1) => ‖x‖)) := by
  constructor
  intro r
  rw [Measure.map_apply measurable_norm (measurableSet_singleton r)]
  have heq : (fun x : Space (n+1) => ‖x‖) ⁻¹' {r} = sphere 0 r := by
    ext x
    simp only [mem_preimage,mem_singleton_iff,mem_sphere,dist_zero_right]
  rw [heq,Measure.restrict_apply isClosed_sphere.measurableSet]
  exact measure_mono_null inter_subset_left (Measure.addHaar_sphere volume (0 : Space (n+1)) r)

/-- The mass of the actual radial cut varies continuously on every bounded
radius interval. No regularity of the measurable shading boundary is needed. -/
theorem continuous_ball_mass {n : ℕ} {Y : Set (Space (n+1))}
    (hfinite : volume Y ≠ ∞) (R : ℝ) :
    ContinuousOn (fun r : ℝ => (volume : Measure (Space (n+1))).real
      (Y ∩ closedBall 0 r)) (Iic R) := by
  let μ : Measure (Space (n+1)) := volume.restrict Y
  let : IsFiniteMeasure μ := isFiniteMeasure_restrict.mpr hfinite
  let ν : Measure ℝ := μ.map (fun x => ‖x‖)
  let : NullSingletonClass ν := radial_no_atoms Y
  have hid (r : ℝ) : ν.real (Iic r) = (volume : Measure (Space (n+1))).real
      (Y ∩ closedBall 0 r) := by
    rw [show ν = μ.map (fun x => ‖x‖) by rfl,
      map_measureReal_apply measurable_norm measurableSet_Iic]
    have heq : (fun x : Space (n+1) => ‖x‖) ⁻¹' Iic r = closedBall 0 r := by
      ext x
      simp only [mem_preimage,mem_Iic,mem_closedBall,dist_zero_right]
    rw [heq,show μ=volume.restrict Y by rfl,measureReal_restrict_apply measurableSet_closedBall,
      inter_comm]
  have hint : IntegrableOn (fun _ : ℝ => (1:ℝ)) (Iic R) ν := (integrable_const 1).integrableOn
  have hc := hint.continuousOn_Iic_primitive_Iic
  simpa only [integral_const,measureReal_restrict_apply_univ,smul_eq_mul,mul_one,hid] using hc

/-- An actual measurable radial cut realizes every prescribed mass between zero
and the mass of a bounded measurable shading, including both endpoints. -/
theorem exists_exact_subset {n : ℕ} {Y : Set (Space (n+1))} {a : ℝ}
    (hY : MeasurableSet Y) (hbounded : Bornology.IsBounded Y)
    (ha : 0 ≤ a) (hle : a ≤ (volume : Measure (Space (n+1))).real Y) :
    ∃ Z : Set (Space (n+1)), MeasurableSet Z ∧ Z ⊆ Y ∧ volume Z ≠ ∞ ∧
      (volume : Measure (Space (n+1))).real Z = a := by
  obtain ⟨R,hR,hYR⟩ := hbounded.subset_closedBall_lt 0 (0 : Space (n+1))
  have hfinite : volume Y ≠ ∞ := measure_ne_top_of_subset hYR measure_closedBall_lt_top.ne
  let f : ℝ → ℝ := fun r => (volume : Measure (Space (n+1))).real (Y ∩ closedBall 0 r)
  have hf : ContinuousOn f (Icc 0 R) :=
    (continuous_ball_mass hfinite R).mono Icc_subset_Iic_self
  have hzero : f 0 = 0 := by
    have hz : volume (Y ∩ closedBall (0 : Space (n+1)) 0) = 0 :=
      measure_mono_null inter_subset_right (by simp)
    simp only [f,measureReal_def,hz,ENNReal.toReal_zero]
  have htop : f R = (volume : Measure (Space (n+1))).real Y := by
    dsimp [f]
    rw [inter_eq_left.mpr hYR]
  have hamem : a ∈ Icc (f 0) (f R) := by rw [hzero,htop]; exact ⟨ha,hle⟩
  obtain ⟨r,_,hr⟩ := intermediate_value_Icc hR.le hf hamem
  exact ⟨Y ∩ closedBall 0 r,hY.inter measurableSet_closedBall,inter_subset_left,
    measure_ne_top_of_subset inter_subset_left hfinite,hr⟩


/-- The original tube family remains a parameter, so cap bounds, direction
separation and base locations are literally unchanged. -/
structure Output {n M : ℕ} (F : TubeFamily (n+1) M)
    (Y : Fin M → Set (Space (n+1))) (radius a : ℝ) where
  shading : Fin M → Set (Space (n+1))
  measurable : ∀ i, MeasurableSet (shading i)
  subset_original : ∀ i, shading i ⊆ Y i
  subset_carrier : ∀ i, shading i ⊆ (F.tube i).carrier radius
  finite_volume : ∀ i, volume (shading i) ≠ ∞
  exact_volume : ∀ i, (volume : Measure (Space (n+1))).real (shading i) = a

/-- Simultaneous exact trimming of every actual measurable tube shading. The
ambient dimension is positive; no such assertion is made for atomic Space 0. -/
theorem construct {n M : ℕ} (F : TubeFamily (n+1) M)
    (Y : Fin M → Set (Space (n+1))) {radius a : ℝ}
    (hY : ∀ i, MeasurableSet (Y i))
    (hsub : ∀ i, Y i ⊆ (F.tube i).carrier radius)
    (ha : 0 ≤ a) (hle : ∀ i, a ≤ (volume : Measure (Space (n+1))).real (Y i)) :
    Nonempty (Output F Y radius a) := by
  have hex (i : Fin M) := exists_exact_subset (hY i)
    ((TubeVolume.carrier_compact (F.tube i) radius).isBounded.subset (hsub i)) ha (hle i)
  choose Z hm hs hf he using hex
  exact ⟨⟨Z,hm,hs,fun i => (hs i).trans (hsub i),hf,he⟩⟩

namespace Output
variable {n M : ℕ} {F : TubeFamily (n+1) M}
  {Y : Fin M → Set (Space (n+1))} {radius a : ℝ}

/-- Exact containment in the same original union, without enlarging cells or
changing tube positions. -/
theorem union_subset (O : Output F Y radius a) :
    (⋃ i, O.shading i) ⊆ ⋃ i, Y i :=
  iUnion_mono O.subset_original

theorem union_volume_le (O : Output F Y radius a)
    (hsub : ∀ i, Y i ⊆ (F.tube i).carrier radius) :
    (volume : Measure (Space (n+1))).real (⋃ i, O.shading i) ≤
      (volume : Measure (Space (n+1))).real (⋃ i, Y i) := by
  have hfin : volume (⋃ i, Y i) ≠ ∞ := by
    simpa only [Set.biUnion_univ] using measure_biUnion_ne_top (μ:=volume)
      (s:=Set.univ) (f:=Y) Set.finite_univ
      (fun i _ => measure_ne_top_of_subset (hsub i) (TubeVolume.carrier_finite (F.tube i) radius))
  exact measureReal_mono O.union_subset hfin

/-- The simultaneous construction gives the exact original-index population
normalization, including the empty-family case. -/
theorem total_volume (O : Output F Y radius a) :
    (∑ i, (volume : Measure (Space (n+1))).real (O.shading i)) = (M:ℝ)*a := by
  simp only [O.exact_volume,Finset.sum_const,Finset.card_univ,Fintype.card_fin,nsmul_eq_mul]

/-- Literal subset monotonicity gives the sharp old-mass/new-mass transfer.
The premise may cover any chosen range of radii. -/
theorem two_ends_ratio (O : Output F Y radius a) {B alpha : ℝ}
    (ha : 0 < a) (hsub : ∀ i, Y i ⊆ (F.tube i).carrier radius)
    (i : Fin M) (x : Space (n+1)) (r : ℝ)
    (hends : (volume : Measure (Space (n+1))).real (Y i ∩ closedBall x r) ≤
      B*r^alpha*(volume : Measure (Space (n+1))).real (Y i)) :
    (volume : Measure (Space (n+1))).real (O.shading i ∩ closedBall x r) ≤
      (B*((volume : Measure (Space (n+1))).real (Y i)/a))*r^alpha*
        (volume : Measure (Space (n+1))).real (O.shading i) := by
  have hfin := measure_ne_top_of_subset (hsub i) (TubeVolume.carrier_finite (F.tube i) radius)
  have hh := measureReal_mono (inter_subset_inter_left (closedBall x r) (O.subset_original i))
    (measure_ne_top_of_subset inter_subset_left hfin)
  refine (hh.trans hends).trans_eq ?_
  rw [O.exact_volume]
  field_simp [ha.ne']

/-- A common upper mass U gives the uniform inherited coefficient B*U/a,
with exact new mass a and every old radius test preserved. -/
theorem two_ends_upper (O : Output F Y radius a) {B alpha U : ℝ}
    (ha : 0 < a) (hB : 0 ≤ B)
    (hsub : ∀ i, Y i ⊆ (F.tube i).carrier radius)
    (hupper : ∀ i, (volume : Measure (Space (n+1))).real (Y i) ≤ U)
    (i : Fin M) (x : Space (n+1)) {r : ℝ} (hr : 0 ≤ r)
    (hends : (volume : Measure (Space (n+1))).real (Y i ∩ closedBall x r) ≤
      B*r^alpha*(volume : Measure (Space (n+1))).real (Y i)) :
    (volume : Measure (Space (n+1))).real (O.shading i ∩ closedBall x r) ≤
      (B*U/a)*r^alpha*(volume : Measure (Space (n+1))).real (O.shading i) := by
  have hh := O.two_ends_ratio ha hsub i x r hends
  have hm := mul_le_mul_of_nonneg_left
    (div_le_div_of_nonneg_right (hupper i) ha.le) hB
  have hm' := mul_le_mul_of_nonneg_right hm (Real.rpow_nonneg hr alpha)
  have hm'' := mul_le_mul_of_nonneg_right hm' (measureReal_nonneg (μ:=(volume : Measure (Space (n+1)))) (s:=O.shading i))
  exact hh.trans (hm''.trans_eq (by ring))

end Output

end
end KakeyaFormal.MeasurableDensityTrimming
