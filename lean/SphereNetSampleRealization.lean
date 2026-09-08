import SamplingLengthAssembly
import SphereNetCapTests
import SamplingRealization
import GridGeometry

/-!
# Source geometry from the same sphere-net-tested raw outcome

The output retains the actual original bounded-variable-length axes, grid labels,
raw probabilities and whole-sphere net. Its sole sampling certificate is the
source-strength SampleGood band [mean/2, 2*mean]; there is no narrow-density
field or independent second sample. This is a geometric realization adapter,
not a theorem asserting existence of a good outcome.
-/
namespace KakeyaFormal.SphereNetSampleRealization
open ProjectiveSphereNet
open Finset SamplingLengthInput SamplingNormalizedMeans SamplingSupport KakeyaSamplingApplication SamplingMeasurableAssembly
open scoped BigOperators
noncomputable section
open Classical

structure Output {n M : ℕ} (F : TubeFamily (n+1) M)
    (Full G : Fin M → Set (Space (n+1))) (δ width R L B alpha theta : ℝ)
    (net : Net n theta) where
  depth : ℕ
  bottom : δ ≤ Localization.radius depth 0
  bottom_upper : Localization.radius depth 0 < 2*δ
  depth_bound : (depth:ℝ) ≤ Real.log (1/δ)/Real.log 2
  omega : Outcome (Fin M) ↥(SamplingBoundedSupport.support Full δ (pointRadius width R L))
  good : SampleGood (SamplingLengthInput.rawFull Full δ width R L) (SamplingLengthInput.rawMarked Full G δ width R L)
    (KakeyaSamplingDichotomy.high (markedMean (SamplingLengthInput.rawMarked Full G δ width R L)) (threshold n δ))
    (SamplingBallTests.mask δ) (SphereNetCapTests.cap net F)
    (ballCutoff (J:=depth) (SamplingLengthInput.rawFull Full δ width R L) B alpha) omega

variable {n M : ℕ} {F : TubeFamily (n+1) M} {Full G : Fin M → Set (Space (n+1))}
variable {δ width R L lam c₀ C₀ xi B alpha K beta theta : ℝ}
variable {length : Fin M → ℝ}
variable {net : Net n theta}

/-- Package exactly the supplied original outcome and its source-strength
certificate; no new sample or stronger per-tube density band is selected. -/
def of_sample (net : Net n theta) (J : ℕ)
    (hb : δ ≤ Localization.radius J 0) (hu : Localization.radius J 0 < 2*δ)
    (hd : (J:ℝ) ≤ Real.log (1/δ)/Real.log 2)
    (omega : Outcome (Fin M) ↥(SamplingBoundedSupport.support Full δ (pointRadius width R L)))
    (good : SampleGood (SamplingLengthInput.rawFull Full δ width R L)
      (SamplingLengthInput.rawMarked Full G δ width R L)
      (KakeyaSamplingDichotomy.high (markedMean (SamplingLengthInput.rawMarked Full G δ width R L))
        (threshold n δ)) (SamplingBallTests.mask δ) (SphereNetCapTests.cap net F)
      (ballCutoff (J:=J) (SamplingLengthInput.rawFull Full δ width R L) B alpha) omega) :
    Output F Full G δ width R L B alpha theta net :=
  ⟨J, hb, hu, hd, omega, good⟩

namespace Output
variable (O : Output F Full G δ width R L B alpha theta net)

def family : TubeFamily (n+1) M :=
  SamplingRealization.full F.tube (SamplingBoundedSupport.support Full δ (pointRadius width R L)) O.omega

def marks (i : Fin M) : Finset (Cell (n+1)) :=
  SamplingRealization.marks (SamplingBoundedSupport.support Full δ (pointRadius width R L))
    (KakeyaSamplingDichotomy.high (markedMean (SamplingLengthInput.rawMarked Full G δ width R L)) (threshold n δ)) O.omega i

theorem axes (i : Fin M) : (O.family.tube i) = F.tube i := rfl

theorem support_and_marks : O.family.unionCells ⊆ SamplingBoundedSupport.support Full δ (pointRadius width R L) ∧
    ∀ i, O.marks i ⊆ O.family.shade i :=
  SamplingRealization.support_and_marks _ _ _ _

theorem separated {sep : ℝ} (hsep : F.Separated (sep*δ)) : O.family.Separated (sep*δ) := hsep

theorem cap_bound {m A : ℝ} (hcap : F.CapBound δ m A) : O.family.CapBound δ m A := hcap

theorem bounded (hb : F.Bounded R) : O.family.Bounded R := hb

/-- Original labels make the support-cardinality comparison exact. -/
theorem union_card : O.family.unionCells.card ≤ (SamplingBoundedSupport.support Full δ (pointRadius width R L)).card :=
  card_le_card O.support_and_marks.1

/-- The union of selected whole cells is contained in the available cell
union. This makes no inclusion claim into the original measurable shadings. -/
theorem cell_union_subset :
    GridShadingMeasure.cellUnion δ O.family.unionCells ⊆
      GridShadingMeasure.cellUnion δ (SamplingBoundedSupport.support Full δ (pointRadius width R L)) :=
  GridShadingMeasure.cellUnion_mono δ O.support_and_marks.1

/-- A selected label still records an actual positive full intersection. -/
theorem full_positive (hδ : 0 < δ) (i : Fin M) {z : Cell (n+1)}
    (hz : z ∈ O.family.shade i) :
    0 < (MeasureTheory.volume : MeasureTheory.Measure (Space (n+1))).real
      (Full i ∩ GridCells.gridCell δ z) := by
  obtain ⟨c,hc,rfl⟩ := mem_map.mp hz
  have hp := O.good.full_support i c hc
  exact (div_pos_iff_of_pos_right (pow_pos hδ (n+1))).mp hp

/-- Marks likewise retain their own positive original marked intersection. -/
theorem marked_positive (hδ : 0 < δ) (i : Fin M) {z : Cell (n+1)}
    (hz : z ∈ O.marks i) :
    0 < (MeasureTheory.volume : MeasureTheory.Measure (Space (n+1))).real
      (G i ∩ GridCells.gridCell δ z) := by
  obtain ⟨c,hc,rfl⟩ := mem_map.mp hz
  have hp := O.good.marked_support i c hc
  exact (div_pos_iff_of_pos_right (pow_pos hδ (n+1))).mp hp

/-- The actual grid labels give a fixed longitudinal mesh-interval count,
with no tube-to-grid alignment requirement. -/
theorem longitudinal_count (hδ : 0 < δ) (i : Fin M) (a : ℝ) :
    ((O.family.shade i).filter (fun z => ∃ t ∈ Set.Icc a (a+δ),
      dist (cellCenter δ z) ((F.tube i).axisPoint t) ≤ (width+((n+1:ℕ):ℝ)/2)*δ)).card ≤
        (2*Nat.ceil (width+((n+1:ℕ):ℝ)/2+1)+3)^(n+1) := by
  apply GridGeometry.one_mesh_interval_grid_count (F.tube i) hδ
  intro z hz
  exact (mem_filter.mp hz).2

variable (h : SamplingLengthInput.Input F length Full G δ width R L lam c₀ C₀ xi B alpha K beta)
include h

/-- Every selected original cell center lies in the fixed tube enlargement. -/
theorem admissible : ∀ i z, z ∈ O.family.shade i →
    ∃ t ∈ Set.Icc (0:ℝ) (length i),
      dist (cellCenter δ z) ((F.tube i).axisPoint t) ≤ (width+((n+1:ℕ):ℝ)/2)*δ := by
  intro i z hz
  obtain ⟨x,hx,hcell⟩ := SamplingSupport.positive_intersection_nonempty (O.full_positive h.scale_pos i hz)
  obtain ⟨t,ht,hd⟩ := h.full_subset i hx
  refine ⟨t,ht,?_⟩
  have hc := GridCells.cell_center_distance hcell
  have htri := dist_triangle (cellCenter δ z) x ((F.tube i).axisPoint t)
  rw [dist_comm (cellCenter δ z) x] at htri
  nlinarith

/-- Literal source density constants, derived only from the broad mean band
contained in SampleGood and the actual original physical full masses. -/
theorem density (i : Fin M) : c₀*lam/(2*δ) ≤ (O.family.shade i).card ∧
    ((O.family.shade i).card:ℝ) ≤ 2*C₀*lam/δ := by
  have hc := (SamplingRealization.counts F.tube _ _ _ _ _ _ _ O.omega O.good).1 i
  have hm := h.full_mean_bounds i
  constructor
  · exact (by ring : c₀*lam/(2*δ)=(c₀*lam/δ)/2).trans_le
      ((div_le_div_of_nonneg_right hm.1 (by norm_num)).trans hc.1)
  · exact (hc.2.trans (mul_le_mul_of_nonneg_left hm.2 (by norm_num))).trans_eq (by ring)

/-- The high sample retains one quarter of the exact original marked mass. -/
theorem marked_mass :
    ((∑ i, (MeasureTheory.volume : MeasureTheory.Measure (Space (n+1))).real (G i))/δ^(n+1))/4 ≤
      ∑ i, ((O.marks i).card:ℝ) := by
  have hh := (SamplingRealization.counts F.tube _ _ _ _ _ _ _ O.omega O.good).2.1
  rwa [h.marked_mean_eq] at hh

theorem marked_density : (xi*lam*(M:ℝ)/δ)/4 ≤ ∑ i, ((O.marks i).card:ℝ) := by
  have hm := div_le_div_of_nonneg_right (h.marked_mean_lower) (by norm_num : (0:ℝ)≤4)
  exact hm.trans (SamplingRealization.counts F.tube _ _ _ _ _ _ _ O.omega O.good).2.1

/-- The middle inequality in source (6.9), retaining the literal Wg. -/
theorem relative_le_marked_expectation : (xi/(8*C₀))*(∑ i, ((O.family.shade i).card:ℝ)) ≤
    ((∑ i, (MeasureTheory.volume : MeasureTheory.Measure (Space (n+1))).real (G i))/δ^(n+1))/4 := by
  have hsum : (∑ i, ((O.family.shade i).card:ℝ)) ≤ 2*C₀*lam*(M:ℝ)/δ := by
    have hh := sum_le_sum (fun i (_ : i ∈ univ) => (O.density h i).2)
    simp only [sum_const,card_univ,Fintype.card_fin,nsmul_eq_mul] at hh
    exact hh.trans_eq (by ring)
  have hcoef : 0 ≤ xi/(8*C₀) := div_nonneg h.marked_fraction_pos.le (by positivity [h.upper_constant_pos])
  have hh := mul_le_mul_of_nonneg_left hsum hcoef
  have he : (xi/(8*C₀))*(2*C₀*lam*(M:ℝ)/δ) = (xi*lam*(M:ℝ)/δ)/4 := by
    field_simp [h.upper_constant_pos.ne']
    ring
  have hlo := h.marked_mean_lower
  rw [h.marked_mean_eq] at hlo
  exact (hh.trans_eq he).trans (div_le_div_of_nonneg_right hlo (by norm_num))

/-- Source relative marked population, with exactly xi/(8 C0). -/
theorem marked_relative : (xi/(8*C₀))*(∑ i, ((O.family.shade i).card:ℝ)) ≤
    ∑ i, ((O.marks i).card:ℝ) :=
  (O.relative_le_marked_expectation h).trans (O.marked_mass h)

/-- All physical ball tests down to delta survive, with a dimension-only
coefficient when alpha≤1. -/
theorem two_ends (ha1 : alpha ≤ 1) :
    ∀ (i : Fin M) (x : Space (n+1)) (r : ℝ), δ ≤ r → r ≤ 1 →
      (((O.family.shade i).filter (fun z => dist (cellCenter δ z) x ≤ r)).card:ℝ) ≤
        (8*ballCoefficient n)*B*r^alpha*((O.family.shade i).card:ℝ) := by
  intro i x r hr hr1
  have hh := SamplingRealization.two_ends F.tube _ h.scale_pos O.bottom_upper.le
    (ballCoefficient_pos n).le (zero_le_one.trans h.two_ends_constant) h.two_ends_exponent
    (SamplingLengthInput.rawFull Full δ width R L) (SamplingLengthInput.rawMarked Full G δ width R L)
    (fun i z => (h.probabilities i z).1.trans (h.probabilities i z).2.1)
    _ _ O.omega O.good i x r hr hr1
  have hp : (4:ℝ)^alpha ≤ 4 := by
    simpa only [Real.rpow_one] using Real.rpow_le_rpow_of_exponent_le (by norm_num : (1:ℝ)≤4) ha1
  have hr0 : 0≤r := h.scale_pos.le.trans hr
  have hcoef : 2*(4:ℝ)^alpha*ballCoefficient n ≤ 8*ballCoefficient n := by
    have hbc := (ballCoefficient_pos n).le
    nlinarith
  have hB0 : 0 ≤ B := zero_le_one.trans h.two_ends_constant
  exact hh.trans (mul_le_mul_of_nonneg_right
    (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hcoef hB0)
      (Real.rpow_nonneg hr0 _)) (Nat.cast_nonneg _))

omit h in
/-- Closed projective caps at the exact source theta for this same net-tested
outcome. No original-direction cap test or narrow-density premise is substituted. -/
theorem closed_broadness :
    ∀ (z : Cell (n+1)) (v : Space (n+1)), ‖v‖=1 →
      (((univ.filter (fun i => z ∈ O.marks i)).filter (fun i =>
        projectiveDistance v (O.family.tube i).direction ≤ theta)).card:ℝ) ≤
          ((univ.filter (fun i => z ∈ O.marks i)).card:ℝ)/10 := by
  intro z v hv
  let E := SamplingBoundedSupport.support Full δ (pointRadius width R L)
  let high := KakeyaSamplingDichotomy.high (markedMean (SamplingLengthInput.rawMarked Full G δ width R L))
    (threshold n δ)
  by_cases hz : z ∈ E
  · let c : ↥E := ⟨z,hz⟩
    have heq : univ.filter (fun i => z ∈ O.marks i) = SamplingCapTests.row high O.omega c := by
      ext i
      simp only [SamplingCapTests.row,mem_filter,mem_univ,true_and]
      exact SamplingRealization.mem_unlabel E _ c
    rw [heq]
    exact SphereNetCapTests.sampled_closed_broadness net F _ _ high _ _ O.omega O.good c v hv
  · have heq : univ.filter (fun i => z ∈ O.marks i) = ∅ := by
      apply filter_eq_empty_iff.mpr
      intro i _ hi
      exact hz (SamplingRealization.unlabel_subset E _ hi)
    simp [heq]

omit h in
/-- The same source bound for open caps at every unit center follows from
inclusion in the already controlled closed cap. -/
theorem broadness :
    ∀ (z : Cell (n+1)) (v : Space (n+1)), ‖v‖=1 →
      (((univ.filter (fun i => z ∈ O.marks i)).filter (fun i =>
        projectiveDistance v (O.family.tube i).direction < theta)).card:ℝ) ≤
          ((univ.filter (fun i => z ∈ O.marks i)).card:ℝ)/10 := by
  intro z v hv
  have hsub : (univ.filter (fun i => z ∈ O.marks i)).filter (fun i =>
      projectiveDistance v (O.family.tube i).direction < theta) ⊆
        (univ.filter (fun i => z ∈ O.marks i)).filter (fun i =>
          projectiveDistance v (O.family.tube i).direction ≤ theta) := by
    intro i hi
    exact mem_filter.mpr ⟨(mem_filter.mp hi).1, (mem_filter.mp hi).2.le⟩
  exact (Nat.cast_le.mpr (card_le_card hsub)).trans (O.closed_broadness z v hv)

end Output
end
end KakeyaFormal.SphereNetSampleRealization
