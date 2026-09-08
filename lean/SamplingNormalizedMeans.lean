import SamplingMeans
import SamplingRowNormalization
import SamplingTheta

/-! Original measurable shading data instantiate equalized sampling means.
All probability, mass and ball/cap expectation inputs come from actual cell
intersections and physical geometry; no expected-value oracle is supplied. -/
namespace KakeyaFormal.SamplingNormalizedMeans
open Finset SamplingSupport SamplingMeans KakeyaSamplingApplication MeasureTheory
open scoped BigOperators ENNReal
noncomputable section
open Classical

/-- Only actual original measurable geometry and conditioning. -/
structure Input {n M : ℕ} (F : TubeFamily (n+1) M)
    (Full G : Fin M → Set (Space (n+1)))
    (δ width R lam c₀ C₀ xi B alpha K beta : ℝ) : Prop where
  scale_pos : 0 < δ
  scale_le_one : δ ≤ 1
  width_nonneg : 0 ≤ width
  density_pos : 0 < lam
  density_le_one : lam ≤ 1
  lower_constant_pos : 0 < c₀
  upper_constant_pos : 0 < C₀
  count_pos : 0 < M
  marked_fraction_pos : 0 < xi
  bounded : F.Bounded R
  full_subset : ∀ i, Full i ⊆ (F.tube i).carrier (width*δ)
  full_measurable : ∀ i, MeasurableSet (Full i)
  marked_measurable : ∀ i, MeasurableSet (G i)
  marked_subset : ∀ i, G i ⊆ Full i
  full_mass : ∀ i, c₀*lam*δ^n ≤ (volume : Measure (Space (n+1))).real (Full i) ∧
    (volume : Measure (Space (n+1))).real (Full i) ≤ C₀*lam*δ^n
  marked_mass : xi*lam*δ^n*(M:ℝ) ≤ ∑ i, (volume : Measure (Space (n+1))).real (G i)
  two_ends_constant : 1 ≤ B
  two_ends_exponent : 0 ≤ alpha
  broadness_constant : 0 < K
  broadness_exponent : 0 < beta
  two_ends : ∀ i x r, δ ≤ r → r ≤ 1 →
    (volume : Measure (Space (n+1))).real (Full i ∩ Metric.closedBall x r) ≤
      B*r^alpha*(volume : Measure (Space (n+1))).real (Full i)
  broadness : ∀ᵐ x ∂(volume : Measure (Space (n+1))),
    ∀ v : Space (n+1), ‖v‖=1 → ∀ r : ℝ, δ ≤ r → r ≤ 1 →
      ((univ.filter (fun i => x ∈ G i ∧ projectiveDistance (F.tube i).direction v ≤ r)).card : ℝ) ≤
        K*r^beta*((univ.filter (fun i => x ∈ G i)).card : ℝ)

def equalizer (c₀ : ℝ) : ℝ := min c₀ 1
def ratio (c₀ C₀ : ℝ) : ℝ := C₀/equalizer c₀
def commonMean (c₀ lam δ : ℝ) : ℝ := equalizer c₀*lam/δ

def rawFull {n M : ℕ} (F : TubeFamily (n+1) M)
    (Full : Fin M → Set (Space (n+1))) (δ width R : ℝ) :
    Fin M → ↥(support F.tube Full δ width R) → ℝ :=
  weights Full δ (support F.tube Full δ width R)

def rawMarked {n M : ℕ} (F : TubeFamily (n+1) M)
    (Full G : Fin M → Set (Space (n+1))) (δ width R : ℝ) :
    Fin M → ↥(support F.tube Full δ width R) → ℝ :=
  weights G δ (support F.tube Full δ width R)

def full {n M : ℕ} (F : TubeFamily (n+1) M)
    (Full : Fin M → Set (Space (n+1))) (δ width R c₀ lam : ℝ) :
    Fin M → ↥(support F.tube Full δ width R) → ℝ :=
  SamplingRowNormalization.full (rawFull F Full δ width R) (commonMean c₀ lam δ)

def marked {n M : ℕ} (F : TubeFamily (n+1) M)
    (Full G : Fin M → Set (Space (n+1))) (δ width R c₀ lam : ℝ) :
    Fin M → ↥(support F.tube Full δ width R) → ℝ :=
  SamplingRowNormalization.marked (rawFull F Full δ width R) (rawMarked F Full G δ width R)
    (commonMean c₀ lam δ)

variable {n M : ℕ} {F : TubeFamily (n+1) M} {Full G : Fin M → Set (Space (n+1))}
variable {δ width R lam c₀ C₀ xi B alpha K beta : ℝ}

namespace Input
variable (h : Input F Full G δ width R lam c₀ C₀ xi B alpha K beta)
include h

theorem equalizer_pos : 0 < equalizer c₀ := lt_min h.lower_constant_pos zero_lt_one

omit h in
theorem equalizer_le_one : equalizer c₀ ≤ 1 := min_le_right _ _

/-- Nonempty actual full masses force the expected ordering of normalization
constants; no independent comparability premise is added. -/
theorem constants_order : c₀ ≤ C₀ := by
  let i : Fin M := ⟨0,h.count_pos⟩
  have hh := (h.full_mass i).1.trans (h.full_mass i).2
  have hp : 0 < lam*δ^n := mul_pos h.density_pos (pow_pos h.scale_pos n)
  nlinarith

theorem ratio_ge_one : 1 ≤ ratio c₀ C₀ :=
  (one_le_div h.equalizer_pos).mpr ((min_le_left _ _).trans h.constants_order)

theorem ratio_pos : 0 < ratio c₀ C₀ := zero_lt_one.trans_le h.ratio_ge_one

theorem commonMean_pos : 0 < commonMean c₀ lam δ :=
  div_pos (mul_pos h.equalizer_pos h.density_pos) h.scale_pos

theorem raw_mean_bounds (i : Fin M) :
    commonMean c₀ lam δ ≤ fullMean (rawFull F Full δ width R) i ∧
      fullMean (rawFull F Full δ width R) i ≤ ratio c₀ C₀*commonMean c₀ lam δ := by
  obtain ⟨hlo,hhi⟩ := fullMean_density F.tube Full h.scale_pos h.scale_le_one h.width_nonneg
    h.bounded h.full_subset h.full_measurable h.full_mass i
  constructor
  · have hh := mul_le_mul_of_nonneg_right (min_le_left c₀ 1) h.density_pos.le
    exact (div_le_div_of_nonneg_right hh h.scale_pos.le).trans hlo
  · have hc := h.equalizer_pos
    have he : ratio c₀ C₀*commonMean c₀ lam δ = C₀*lam/δ := by
      unfold ratio commonMean
      field_simp
    rw [he]
    exact hhi

theorem raw_probabilities (i : Fin M) (z : ↥(support F.tube Full δ width R)) :
    0 ≤ rawMarked F Full G δ width R i z ∧
      rawMarked F Full G δ width R i z ≤ rawFull F Full δ width R i z ∧
      rawFull F Full δ width R i z ≤ 1 :=
  coupled_weights (h.marked_subset i) h.scale_pos z.val

/-- All equalized probabilities are genuinely nested and bounded by one. -/
theorem normalized_probabilities (i : Fin M) (z : ↥(support F.tube Full δ width R)) :
    0 ≤ marked F Full G δ width R c₀ lam i z ∧
      marked F Full G δ width R c₀ lam i z ≤ full F Full δ width R c₀ lam i z ∧
      full F Full δ width R c₀ lam i z ≤ 1 :=
  SamplingRowNormalization.probabilities _ _ h.commonMean_pos (fun i => (h.raw_mean_bounds i).1)
    (fun i z => (h.raw_probabilities i z).1) (fun i z => (h.raw_probabilities i z).2.1)
    (fun i z => (h.raw_probabilities i z).2.2) i z

/-- Full means are exactly equal, with every original tube index retained. -/
theorem normalized_full_mean (i : Fin M) :
    fullMean (full F Full δ width R c₀ lam) i = commonMean c₀ lam δ :=
  SamplingRowNormalization.full_mean _ (fun i => (h.commonMean_pos.trans_le (h.raw_mean_bounds i).1).ne') i

/-- Equalization only reduces probabilities, preserving the required original
physical support bound for the realization geometry. -/
theorem normalized_full_le_weight (i : Fin M) (z : ↥(support F.tube Full δ width R)) :
    full F Full δ width R c₀ lam i z ≤ weight (Full i) δ z.val := by
  have hh := (SamplingRowNormalization.factor_bounds _ h.commonMean_pos h.ratio_pos h.raw_mean_bounds i).2.1
  exact (mul_le_mul_of_nonneg_right hh (weight_nonneg (Full i) h.scale_pos z.val)).trans_eq (one_mul _)

/-- Positive full support is exactly the original positive-measure incidence. -/
theorem normalized_full_support (i : Fin M) (z : ↥(support F.tube Full δ width R)) :
    0 < full F Full δ width R c₀ lam i z ↔
      0 < (volume : Measure (Space (n+1))).real (Full i ∩ GridCells.gridCell δ z.val) := by
  unfold full
  rw [SamplingRowNormalization.full_support _ h.commonMean_pos
    (fun i => h.commonMean_pos.trans_le (h.raw_mean_bounds i).1) i z]
  exact div_pos_iff_of_pos_right (pow_pos h.scale_pos (n+1))

/-- The normalized marks retain at least the fixed fraction equalizer/C0 of
the actual original total marked mass. -/
theorem normalized_marked_mass :
    (equalizer c₀/C₀)*(xi*lam*(M:ℝ)/δ) ≤
      ∑ z : support F.tube Full δ width R, markedMean (marked F Full G δ width R c₀ lam) z := by
  have hm := SamplingRowNormalization.marked_mass_lower (rawFull F Full δ width R)
    (rawMarked F Full G δ width R) h.commonMean_pos h.ratio_pos h.raw_mean_bounds
    (fun i z => (h.raw_probabilities i z).1)
  have he := marked_total_mean F.tube Full G h.scale_pos h.scale_le_one h.width_nonneg
    h.bounded h.full_subset h.marked_measurable h.marked_subset
  change (∑ z, markedMean (rawMarked F Full G δ width R) z) = _ at he
  rw [he] at hm
  have hlo := div_le_div_of_nonneg_right h.marked_mass (pow_pos h.scale_pos (n+1)).le
  have hid : (xi*lam*δ^n*(M:ℝ))/δ^(n+1) = xi*lam*(M:ℝ)/δ := by
    rw [pow_succ]
    field_simp [h.scale_pos.ne']
  rw [hid] at hlo
  have hh := mul_le_mul_of_nonneg_left hlo (div_nonneg (by norm_num : (0:ℝ) ≤ 1) h.ratio_pos.le)
  have hr : 1/ratio c₀ C₀ = equalizer c₀/C₀ := by unfold ratio; field_simp
  rw [hr] at hh hm
  exact hh.trans hm

/-- Exact row scaling preserves the full two-ends expectation coefficient. -/
theorem normalized_ball_mean {J : ℕ} (hbottom : δ ≤ Localization.radius J 0)
    (i : Fin M) (t : SamplingBallTests.Test (support F.tube Full δ width R) J) :
    ballMean (full F Full δ width R c₀ lam) (SamplingBallTests.mask δ) i t ≤
      B*(1+((n+1:ℕ):ℝ)/2)^alpha*(SamplingBallTests.testRadius t)^alpha*commonMean c₀ lam δ := by
  apply SamplingRowNormalization.ball_relative (rawFull F Full δ width R) (SamplingBallTests.mask δ)
    h.commonMean_pos (fun i => h.commonMean_pos.trans_le (h.raw_mean_bounds i).1)
    (fun _ t => B*(1+((n+1:ℕ):ℝ)/2)^alpha*(SamplingBallTests.testRadius t)^alpha) _ i t
  intro i t
  exact SamplingMeans.ballMean_two_ends F.tube Full h.scale_pos h.scale_le_one h.width_nonneg
    h.two_ends_constant h.two_ends_exponent hbottom h.bounded h.full_subset h.full_measurable h.two_ends i t

/-- Integrated broadness loses only the fixed original density ratio after
full and marked probabilities are scaled by the same per-tube factor. -/
theorem normalized_cap_mean {theta : ℝ} (htest : δ ≤ 2*theta) (htest1 : 2*theta ≤ 1)
    (z : ↥(support F.tube Full δ width R)) (a : Fin M) :
    capMean (marked F Full G δ width R c₀ lam) (SamplingCapTests.cap F theta) z a ≤
      (ratio c₀ C₀*K)*(2*theta)^beta*markedMean (marked F Full G δ width R c₀ lam) z := by
  have hraw := SamplingMeans.cap_mean_from_bounded_radii F G h.scale_pos htest htest1 z.val
    h.marked_measurable h.broadness a
  have hnonneg : 0 ≤ K*(2*theta)^beta :=
    mul_nonneg h.broadness_constant.le (Real.rpow_nonneg (by linarith [h.scale_pos] : 0 ≤ 2*theta) _)
  have hh := SamplingRowNormalization.cap_relative (rawFull F Full δ width R)
    (rawMarked F Full G δ width R) (SamplingCapTests.cap F theta)
    h.commonMean_pos h.ratio_pos hnonneg h.raw_mean_bounds
    (fun i z => (h.raw_probabilities i z).1) z a hraw
  exact hh.trans_eq (by dsimp only [marked]; ring)

/-- The literal already-proved theta choice discharges the normalized cap
budget. The only remaining scale prerequisite is its actual bottom-radius test. -/
theorem normalized_cap_test
    (htest : δ ≤ 2*SamplingTheta.choice (ratio c₀ C₀*K) beta)
    (z : ↥(support F.tube Full δ width R)) (a : Fin M) :
    1000*capMean (marked F Full G δ width R c₀ lam)
      (SamplingCapTests.cap F (SamplingTheta.choice (ratio c₀ C₀*K) beta)) z a ≤
        markedMean (marked F Full G δ width R c₀ lam) z := by
  have hrK : 0 < ratio c₀ C₀*K := mul_pos h.ratio_pos h.broadness_constant
  have hupper : 2*SamplingTheta.choice (ratio c₀ C₀*K) beta ≤ 1 := by
    linarith [SamplingTheta.choice_le_hundredth (ratio c₀ C₀*K) beta]
  have hh := h.normalized_cap_mean htest hupper z a
  have hn : 0 ≤ markedMean (marked F Full G δ width R c₀ lam) z :=
    sum_nonneg (fun i _ => (h.normalized_probabilities i z).1)
  have hb := mul_le_mul_of_nonneg_right (SamplingTheta.cap_budget hrK h.broadness_exponent) hn
  nlinarith

/-- The exact original marked volume, not only its stated lower budget, is
retained in the expected mass up to the fixed row ratio. -/
theorem normalized_actual_marked_mass :
    (equalizer c₀/C₀)*((∑ i, (volume : Measure (Space (n+1))).real (G i))/δ^(n+1)) ≤
      ∑ z : support F.tube Full δ width R, markedMean (marked F Full G δ width R c₀ lam) z := by
  have hm := SamplingRowNormalization.marked_mass_lower (rawFull F Full δ width R)
    (rawMarked F Full G δ width R) h.commonMean_pos h.ratio_pos h.raw_mean_bounds
    (fun i z => (h.raw_probabilities i z).1)
  have he := marked_total_mean F.tube Full G h.scale_pos h.scale_le_one h.width_nonneg
    h.bounded h.full_subset h.marked_measurable h.marked_subset
  change (∑ z, markedMean (rawMarked F Full G δ width R) z) = _ at he
  rw [he] at hm
  have hr : 1/ratio c₀ C₀ = equalizer c₀/C₀ := by unfold ratio; field_simp
  rw [hr] at hm
  exact hm

/-- Marking also preserves precisely the positive original marked incidences. -/
theorem normalized_marked_support (i : Fin M) (z : ↥(support F.tube Full δ width R)) :
    0 < marked F Full G δ width R c₀ lam i z ↔
      0 < (volume : Measure (Space (n+1))).real (G i ∩ GridCells.gridCell δ z.val) := by
  unfold marked
  rw [SamplingRowNormalization.marked_support _ _ h.commonMean_pos
    (fun i => h.commonMean_pos.trans_le (h.raw_mean_bounds i).1) i z]
  exact div_pos_iff_of_pos_right (pow_pos h.scale_pos (n+1))

end Input

/-- Fixed dimension-only cutoff coefficient for every alpha between zero and
one. n+1 is the actual ambient dimension. -/
def ballCoefficient (n : ℕ) : ℝ := 4*(1+((n+1:ℕ):ℝ)/2)

theorem ballCoefficient_pos (n : ℕ) : 0 < ballCoefficient n := by unfold ballCoefficient; positivity

namespace Input
variable (h : Input F Full G δ width R lam c₀ C₀ xi B alpha K beta)
include h

/-- The actual ball expectations fit the single cutoff used by the sharp
sampling assembly, with a coefficient independent of alpha∈[0,1]. -/
theorem normalized_ball_test {J : ℕ} (ha1 : alpha ≤ 1)
    (hbottom : δ ≤ Localization.radius J 0)
    (i : Fin M) (t : SamplingBallTests.Test (support F.tube Full δ width R) J) :
    4*ballMean (full F Full δ width R c₀ lam) (SamplingBallTests.mask δ) i t ≤
      ballCoefficient n*B*(SamplingBallTests.testRadius t)^alpha*commonMean c₀ lam δ := by
  have hg1 : 1 ≤ 1+((n+1:ℕ):ℝ)/2 := by
    have hn := Nat.cast_nonneg (α := ℝ) (n+1)
    linarith
  have hg : (1+((n+1:ℕ):ℝ)/2)^alpha ≤ 1+((n+1:ℕ):ℝ)/2 := by
    simpa only [Real.rpow_one] using Real.rpow_le_rpow_of_exponent_le hg1 ha1
  have hB0 : 0 ≤ B := zero_le_one.trans h.two_ends_constant
  have hmu : 0 ≤ commonMean c₀ lam δ := h.commonMean_pos.le
  have hrad : 0 ≤ SamplingBallTests.testRadius t := by
    have hh := (SamplingBallTests.radius_bounds hbottom t).1
    linarith [h.scale_pos]
  calc
    _ ≤ 4*(B*(1+((n+1:ℕ):ℝ)/2)^alpha*(SamplingBallTests.testRadius t)^alpha*commonMean c₀ lam δ) :=
      mul_le_mul_of_nonneg_left (h.normalized_ball_mean hbottom i t) (by norm_num)
    _ ≤ 4*(B*(1+((n+1:ℕ):ℝ)/2)*(SamplingBallTests.testRadius t)^alpha*commonMean c₀ lam δ) := by gcongr
    _ = _ := by unfold ballCoefficient; ring

end Input

/-- One angular scale threshold precedes all actual measurable configurations.
Only the original logarithmic broadness budget is needed, and the doubled-cap
mean tests are concluded rather than assumed. -/
theorem uniform_angular_tests (c₀ C₀ K₀ beta logPower : ℝ)
    (hc₀ : 0 < c₀) (hC₀ : 0 < C₀) (hK₀ : 0 < K₀)
    (hbeta : 0 < beta) (hlog : 0 ≤ logPower) :
    ∃ δ₀ : ℝ, 0 < δ₀ ∧ δ₀ ≤ 1 ∧
      ∀ {n M : ℕ} (F : TubeFamily (n+1) M) (Full G : Fin M → Set (Space (n+1)))
      {δ width R lam xi B alpha K : ℝ},
      Input F Full G δ width R lam c₀ C₀ xi B alpha K beta → δ ≤ δ₀ →
      K ≤ K₀*(Real.log (2/δ))^logPower →
      let theta := SamplingTheta.choice (ratio c₀ C₀*K) beta
      0 < theta ∧ δ ≤ 2*theta ∧ 2*theta ≤ 1 ∧
        SamplingTheta.choice (ratio c₀ C₀*K₀) beta*(Real.log (2/δ))^(-logPower/beta) ≤ theta ∧
        ∀ (z : ↥(support F.tube Full δ width R)) (a : Fin M),
          1000*capMean (marked F Full G δ width R c₀ lam) (SamplingCapTests.cap F theta) z a ≤
            markedMean (marked F Full G δ width R c₀ lam) z := by
  have hratio : 0 < ratio c₀ C₀ := div_pos hC₀ (lt_min hc₀ zero_lt_one)
  obtain ⟨δ₀,hδ₀,hδ₀1,hchoose⟩ := SamplingTheta.uniform_small_scales
    (mul_pos hratio hK₀) hbeta hlog
  refine ⟨δ₀,hδ₀,hδ₀1,?_⟩
  intro n M F Full G δ width R lam xi B alpha K h hscale hbudget theta
  have hbudget' : ratio c₀ C₀*K ≤ (ratio c₀ C₀*K₀)*(Real.log (2/δ))^logPower :=
    (mul_le_mul_of_nonneg_left hbudget hratio.le).trans_eq (by ring)
  obtain ⟨hpos,hbottom,hupper,_,hlower⟩ := hchoose δ (ratio c₀ C₀*K) h.scale_pos hscale
    (mul_pos hratio h.broadness_constant) hbudget'
  exact ⟨hpos,hbottom,hupper,hlower,fun z a => h.normalized_cap_test hbottom z a⟩

end
end KakeyaFormal.SamplingNormalizedMeans
