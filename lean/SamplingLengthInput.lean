import SamplingBoundedSupport

/-! Source physical data for comparable (indeed uniformly upper-bounded)
axis lengths. All means remain the original raw probabilities at the original
mesh; no spatial or row scaling changes the angular tests. -/
namespace KakeyaFormal.SamplingLengthInput
open Finset MeasureTheory SamplingSupport SamplingMeans KakeyaSamplingApplication SamplingNormalizedMeans
open scoped BigOperators
noncomputable section
open Classical

structure Input {n M : ℕ} (F : TubeFamily (n+1) M)
    (length : Fin M → ℝ) (Full G : Fin M → Set (Space (n+1)))
    (δ width R L lam c₀ C₀ xi B alpha K beta : ℝ) : Prop where
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
  length_upper : ∀ i, length i ≤ L
  full_subset : ∀ i, Full i ⊆ SamplingGeometry.lengthCarrier (F.tube i) (length i) (width*δ)
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

/-- Fixed physical support radius, independent of all sampling data. -/
def pointRadius (width R L : ℝ) : ℝ := max 0 R+max 0 L+width+1

theorem pointRadius_pos {width R L : ℝ} (hw : 0 ≤ width) : 0 < pointRadius width R L := by
  unfold pointRadius
  positivity

def rawFull {n M : ℕ} (Full : Fin M → Set (Space (n+1))) (δ width R L : ℝ) :
    Fin M → ↥(SamplingBoundedSupport.support Full δ (pointRadius width R L)) → ℝ :=
  weights Full δ _

def rawMarked {n M : ℕ} (Full G : Fin M → Set (Space (n+1))) (δ width R L : ℝ) :
    Fin M → ↥(SamplingBoundedSupport.support Full δ (pointRadius width R L)) → ℝ :=
  weights G δ _

variable {n M : ℕ} {F : TubeFamily (n+1) M} {length : Fin M → ℝ}
variable {Full G : Fin M → Set (Space (n+1))} {δ width R L lam c₀ C₀ xi B alpha K beta : ℝ}
namespace Input
variable (h : Input F length Full G δ width R L lam c₀ C₀ xi B alpha K beta)
include h

/-- Actual variable-length carriers give the required bounded support. -/
theorem full_bounded (i : Fin M) (x : Space (n+1)) (hx : x ∈ Full i) :
    ‖x‖ ≤ pointRadius width R L := by
  obtain ⟨t,ht,hd⟩ := h.full_subset i hx
  have haxis := norm_add_le (F.tube i).base (t • (F.tube i).direction)
  rw [norm_smul,Real.norm_eq_abs,(F.tube i).unit_direction,mul_one,abs_of_nonneg ht.1] at haxis
  have htri := dist_triangle x ((F.tube i).axisPoint t) 0
  simp only [dist_zero_right,UnitTube.axisPoint] at htri
  dsimp only [UnitTube.axisPoint] at hd
  have htL := ht.2.trans (h.length_upper i)
  have hw := mul_le_mul_of_nonneg_left h.scale_le_one h.width_nonneg
  dsimp [pointRadius]
  nlinarith [h.bounded i,le_max_right (0:ℝ) R,le_max_right (0:ℝ) L]

theorem full_finite (i : Fin M) : (volume : Measure (Space (n+1))) (Full i) ≠ ⊤ := by
  have hsub : Full i ⊆ Metric.closedBall (0:Space (n+1)) (pointRadius width R L) := by
    intro x hx
    simpa only [Metric.mem_closedBall,dist_zero_right] using h.full_bounded i x hx
  exact measure_ne_top_of_subset hsub
    (isCompact_closedBall (0:Space (n+1)) (pointRadius width R L)).measure_ne_top

theorem probabilities (i : Fin M) (z : ↥(SamplingBoundedSupport.support Full δ (pointRadius width R L))) :
    0 ≤ rawMarked Full G δ width R L i z ∧
      rawMarked Full G δ width R L i z ≤ rawFull Full δ width R L i z ∧
      rawFull Full δ width R L i z ≤ 1 :=
  coupled_weights (h.marked_subset i) h.scale_pos z.val

theorem full_mean_eq (i : Fin M) : fullMean (rawFull Full δ width R L) i =
    (volume : Measure (Space (n+1))).real (Full i)/δ^(n+1) :=
  SamplingBoundedSupport.full_mean_eq Full h.scale_pos h.full_bounded Full h.full_measurable
    (fun _ => Set.Subset.rfl) i

theorem full_mean_bounds (i : Fin M) : c₀*lam/δ ≤ fullMean (rawFull Full δ width R L) i ∧
    fullMean (rawFull Full δ width R L) i ≤ C₀*lam/δ := by
  rw [h.full_mean_eq]
  have hid (a : ℝ) : (a*lam*δ^n)/δ^(n+1) = a*lam/δ := by
    rw [pow_succ]
    field_simp [h.scale_pos.ne']
  constructor
  · exact (hid c₀).symm.trans_le (div_le_div_of_nonneg_right (h.full_mass i).1 (pow_pos h.scale_pos (n+1)).le)
  · exact (div_le_div_of_nonneg_right (h.full_mass i).2 (pow_pos h.scale_pos (n+1)).le).trans_eq (hid C₀)

theorem marked_mean_eq :
    (∑ z, markedMean (rawMarked Full G δ width R L) z) =
      (∑ i, (volume : Measure (Space (n+1))).real (G i))/δ^(n+1) :=
  SamplingBoundedSupport.marked_mean_eq Full G h.scale_pos h.full_bounded h.marked_measurable h.marked_subset

theorem marked_mean_lower : xi*lam*(M:ℝ)/δ ≤ ∑ z, markedMean (rawMarked Full G δ width R L) z := by
  rw [h.marked_mean_eq]
  have hlo := div_le_div_of_nonneg_right h.marked_mass (pow_pos h.scale_pos (n+1)).le
  have hid : (xi*lam*δ^n*(M:ℝ))/δ^(n+1) = xi*lam*(M:ℝ)/δ := by
    rw [pow_succ]
    field_simp [h.scale_pos.ne']
  rwa [hid] at hlo

theorem ball_test {J : ℕ} (ha1 : alpha ≤ 1) (hbottom : δ ≤ Localization.radius J 0)
    (i : Fin M) (t : SamplingBallTests.Test (SamplingBoundedSupport.support Full δ (pointRadius width R L)) J) :
    4*ballMean (rawFull Full δ width R L) (SamplingBallTests.mask δ) i t ≤
      ballCoefficient n*B*(SamplingBallTests.testRadius t)^alpha*fullMean (rawFull Full δ width R L) i := by
  have hg1 : 1 ≤ 1+((n+1:ℕ):ℝ)/2 := by have hn := Nat.cast_nonneg (α:=ℝ) (n+1); linarith
  have hg : (1+((n+1:ℕ):ℝ)/2)^alpha ≤ 1+((n+1:ℕ):ℝ)/2 := by
    simpa only [Real.rpow_one] using Real.rpow_le_rpow_of_exponent_le hg1 ha1
  have hB0 : 0 ≤ B := zero_le_one.trans h.two_ends_constant
  have hmu : 0 ≤ fullMean (rawFull Full δ width R L) i :=
    (div_nonneg (mul_nonneg h.lower_constant_pos.le h.density_pos.le) h.scale_pos.le).trans (h.full_mean_bounds i).1
  have hrad : 0 ≤ SamplingBallTests.testRadius t := by
    have hh := (SamplingBallTests.radius_bounds hbottom t).1
    linarith [h.scale_pos]
  have hb := SamplingBoundedSupport.ball_mean_two_ends Full h.scale_pos h.full_bounded h.full_measurable
    h.full_finite h.two_ends_constant h.two_ends_exponent hbottom h.two_ends i t
  calc
    _ ≤ 4*(B*(1+((n+1:ℕ):ℝ)/2)^alpha*(SamplingBallTests.testRadius t)^alpha*fullMean (rawFull Full δ width R L) i) :=
      mul_le_mul_of_nonneg_left hb (by norm_num)
    _ ≤ 4*(B*(1+((n+1:ℕ):ℝ)/2)*(SamplingBallTests.testRadius t)^alpha*fullMean (rawFull Full δ width R L) i) := by gcongr
    _ = _ := by unfold ballCoefficient; ring

theorem cap_test (htest : δ ≤ 2*SamplingTheta.choice K beta)
    (z : ↥(SamplingBoundedSupport.support Full δ (pointRadius width R L))) (a : Fin M) :
    1000*capMean (rawMarked Full G δ width R L) (SamplingCapTests.cap F (SamplingTheta.choice K beta)) z a ≤
      markedMean (rawMarked Full G δ width R L) z := by
  apply SamplingMeans.capMean_admissible F G _ h.scale_pos htest
    (by linarith [SamplingTheta.choice_le_hundredth K beta]) _ h.marked_measurable h.broadness z a
  simpa only [mul_assoc] using SamplingTheta.cap_budget h.broadness_constant h.broadness_exponent

end Input
end
end KakeyaFormal.SamplingLengthInput
