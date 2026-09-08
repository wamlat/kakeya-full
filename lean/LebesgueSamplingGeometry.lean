import LebesgueSamplingSource

/-! Physical guarantees for the original completed-measurable source sample.
All shadings here use the original cell labels and raw outcome, rather than
being renamed outputs of a different representative family. -/
namespace KakeyaFormal.LebesgueSamplingGeometry
open Finset MeasureTheory SamplingLengthInput SamplingSupport SamplingNormalizedMeans
  KakeyaSamplingApplication SamplingMeasurableAssembly
open scoped BigOperators
noncomputable section
open Classical

variable {n M : ℕ} {F : TubeFamily (n+1) M} {Full G : Fin M → Set (Space (n+1))}
variable {δ width R L lam c₀ C₀ xi B alpha K beta theta : ℝ}
variable {length : Fin M → ℝ} {net : ProjectiveSphereNet.Net n theta}
variable (O : SphereNetSampleRealization.Output F Full G δ width R L B alpha theta net)
variable (h : LebesgueSampling.Input F length Full G δ width R L lam c₀ C₀ xi B alpha K beta)
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
  have hm := h.marked_mean_eq
  change (∑ z, markedMean (SamplingLengthInput.rawMarked Full G δ width R L) z) =
    (∑ i, volume.real (G i))/δ^(n+1) at hm
  rwa [hm] at hh

theorem marked_density : (xi*lam*(M:ℝ)/δ)/4 ≤ ∑ i, ((O.marks i).card:ℝ) := by
  have hm := div_le_div_of_nonneg_right (h.marked_mean_lower) (by norm_num : (0:ℝ)≤4)
  exact hm.trans (SamplingRealization.counts F.tube _ _ _ _ _ _ _ O.omega O.good).2.1

/-- The middle inequality in source (6.9), retaining the literal Wg. -/
theorem relative_le_marked_expectation : (xi/(8*C₀))*(∑ i, ((O.family.shade i).card:ℝ)) ≤
    ((∑ i, (MeasureTheory.volume : MeasureTheory.Measure (Space (n+1))).real (G i))/δ^(n+1))/4 := by
  have hsum : (∑ i, ((O.family.shade i).card:ℝ)) ≤ 2*C₀*lam*(M:ℝ)/δ := by
    have hh := sum_le_sum (fun i (_ : i ∈ univ) => (density O h i).2)
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
  (relative_le_marked_expectation O h).trans (marked_mass O h)

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

end
end KakeyaFormal.LebesgueSamplingGeometry
