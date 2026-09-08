import SamplingLengthAssembly
import SamplingRealization
import GridGeometry

/-! Actual source (6.7)–(6.11) from a single raw coupled sample. The tube
indices, axes, original grid labels and probability arrays remain identical. -/
namespace KakeyaFormal.SamplingLengthRealization
open Finset SamplingLengthInput SamplingNormalizedMeans SamplingSupport KakeyaSamplingApplication SamplingMeasurableAssembly
open scoped BigOperators
noncomputable section
open Classical

structure Output {n M : ℕ} (F : TubeFamily (n+1) M)
    (Full G : Fin M → Set (Space (n+1))) (δ width R L B alpha theta : ℝ) where
  depth : ℕ
  bottom : δ ≤ Localization.radius depth 0
  bottom_upper : Localization.radius depth 0 < 2*δ
  depth_bound : (depth:ℝ) ≤ Real.log (1/δ)/Real.log 2
  omega : Outcome (Fin M) ↥(SamplingBoundedSupport.support Full δ (pointRadius width R L))
  good : SampleGood (SamplingLengthInput.rawFull Full δ width R L) (SamplingLengthInput.rawMarked Full G δ width R L)
    (KakeyaSamplingDichotomy.high (markedMean (SamplingLengthInput.rawMarked Full G δ width R L)) (threshold n δ))
    (SamplingBallTests.mask δ) (SamplingCapTests.cap F theta)
    (ballCutoff (J:=depth) (SamplingLengthInput.rawFull Full δ width R L) B alpha) omega
  narrow : ∀ i, (2/3:ℝ)*fullMean (SamplingLengthInput.rawFull Full δ width R L) i ≤ (fullShading omega i).card ∧
    ((fullShading omega i).card:ℝ) ≤ (4/3:ℝ)*fullMean (SamplingLengthInput.rawFull Full δ width R L) i

variable {n M : ℕ} {F : TubeFamily (n+1) M} {Full G : Fin M → Set (Space (n+1))}
variable {δ width R L lam c₀ C₀ xi B alpha K beta theta : ℝ}
variable {length : Fin M → ℝ}

/-- This output carries the actual raw outcome, not merely desired conclusions. -/
theorem realize (hh : SamplingLengthAssembly.HighResult F Full G δ width R L B alpha theta) :
    Nonempty (Output F Full G δ width R L B alpha theta) := by
  obtain ⟨J,hb,hu,hd,omega,hg,hn⟩ := hh
  exact ⟨⟨J,hb,hu,hd,omega,hg,hn⟩⟩

namespace Output
variable (O : Output F Full G δ width R L B alpha theta)

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

/-- Literal source density constants; the stronger narrow band is also retained
in the output certificate. -/
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
/-- All marked row directions satisfy the same literal source open-cap bound. -/
theorem broadness : ∀ (z : Cell (n+1)) (v : Space (n+1)),
    (((univ.filter (fun i => z ∈ O.marks i)).filter (fun i =>
      projectiveDistance v (O.family.tube i).direction < theta)).card:ℝ) ≤
        ((univ.filter (fun i => z ∈ O.marks i)).card:ℝ)/10 :=
  SamplingRealization.broadness F _ theta _ _ _ _ _ O.omega O.good

omit h in
/-- Closed projective caps at the exact source theta, using the same outcome. -/
theorem closed_broadness (ht : 0 < theta) (ht1 : theta ≤ 1) :
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
    exact SamplingClosedCaps.sampled_closed_broadness F ht ht1 _ _ high _ _ O.omega O.good c v hv
  · have heq : univ.filter (fun i => z ∈ O.marks i) = ∅ := by
      apply filter_eq_empty_iff.mpr
      intro i _ hi
      exact hz (SamplingRealization.unlabel_subset E _ hi)
    simp [heq]

end Output
/-- Complete geometric low/high sampling at the manuscript's fixed parameter
range, using the raw probabilities and the literal source theta. Every high
output has all the guarantees proved in Output above, from the same outcome. -/
theorem construct (n : ℕ) (width R L sep c₀ C₀ K₀ beta logPower s alpha : ℝ)
    (hw : 0 ≤ width) (hsep0 : 0 < sep) (hc₀ : 0 < c₀) (hK₀ : 0 < K₀)
    (hbeta : 0 < beta) (hlog : 0 ≤ logPower)
    (hs : 0 < s) (hs1 : s < 1) (ha : 0 ≤ alpha) (hgap : alpha < 1-s) :
    ∃ δ₀ : ℝ, 0 < δ₀ ∧ δ₀ ≤ 1 ∧
      ∀ {M : ℕ} (F : TubeFamily (n+1) M) (length : Fin M → ℝ) (Full G : Fin M → Set (Space (n+1)))
      {δ lam xi B K : ℝ},
      SamplingLengthInput.Input F length Full G δ width R L lam c₀ C₀ xi B alpha K beta →
      F.Separated (sep*δ) → δ ≤ δ₀ → (1/δ)^(-s) ≤ lam →
      K ≤ K₀*(Real.log (2/δ))^logPower →
      let theta := SamplingTheta.choice K beta
      let q := SamplingLengthInput.rawMarked Full G δ width R L
      0 < theta ∧ δ ≤ 2*theta ∧ 2*theta ≤ 1 ∧
      SamplingTheta.choice K₀ beta*(Real.log (2/δ))^(-logPower/beta) ≤ theta ∧
      ((SamplingLengthAssembly.LowResult F Full G δ width R L ∧
        (xi*lam*(M:ℝ)/δ)/(2*threshold n δ) ≤
          ((KakeyaSamplingDichotomy.low (markedMean q) (threshold n δ)).card:ℝ)) ∨
       Nonempty (Output F Full G δ width R L B alpha theta)) := by
  obtain ⟨δ₀,hδ₀,hδ₀1,hall⟩ := SamplingLengthAssembly.construct n width R L sep c₀ C₀ K₀ beta logPower s alpha
    hw hsep0 hc₀ hK₀ hbeta hlog hs hs1 ha hgap
  refine ⟨δ₀,hδ₀,hδ₀1,?_⟩
  intro M F length Full G δ lam xi B K h hsep hsmall hlam hK
  obtain ⟨hp,hl,hu,hlogbound,halt⟩ := hall F length Full G h hsep hsmall hlam hK
  exact ⟨hp,hl,hu,hlogbound,halt.imp_right realize⟩

end
end KakeyaFormal.SamplingLengthRealization
