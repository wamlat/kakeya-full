import Localization

/-! The actual measure-theoretic version of smallest-scale localization.
Finite measure of the original shading is explicit; the ambient measure need
not be finite, so Lebesgue measure on Euclidean space is permitted. -/
open MeasureTheory Set
open scoped ENNReal
namespace KakeyaFormal.MeasurableLocalization
open KakeyaFormal.Localization

variable {X : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X]

/-- The selected restriction is measurable, keeps the scale-normalized mass, and
satisfies the two-ends bound at every radius above the bottom grid scale. -/
theorem smallest_scale_two_ends (μ : Measure X) (Y : Set X)
    (hY : MeasurableSet Y) (hfinite : μ Y ≠ ∞) (J : ℕ)
    {alpha : ℝ} (ha : 0 ≤ alpha) (x₀ : X)
    (hcover : Y ⊆ Metric.closedBall x₀ 1) :
    ∃ j ≤ J, ∃ x : X,
      let Z := Y ∩ Metric.closedBall x (radius J j)
      MeasurableSet Z ∧ (radius J j)^alpha * μ.real Y ≤ μ.real Z ∧
      ∀ y : X, ∀ r : ℝ, radius J 0 ≤ r → r ≤ radius J j →
        μ.real (Z ∩ Metric.closedBall y r) ≤
          (2 : ℝ)^alpha * (r / radius J j)^alpha * μ.real Z := by
  classical
  have htop : Y ∩ Metric.closedBall x₀ (radius J J) = Y := by
    rw [radius_top]
    exact Set.inter_eq_left.mpr hcover
  have hex : ∃ j : ℕ, j ≤ J ∧ ∃ x : X,
      (radius J j)^alpha * μ.real Y ≤ μ.real (Y ∩ Metric.closedBall x (radius J j)) := by
    refine ⟨J,le_rfl,x₀,?_⟩
    rw [htop,radius_top]
    simp
  let j := Nat.find hex
  obtain ⟨hj,x,hmass⟩ := Nat.find_spec hex
  let Z := Y ∩ Metric.closedBall x (radius J j)
  have hZ : Z ⊆ Y := Set.inter_subset_left
  have hZfinite : μ Z ≠ ∞ := measure_ne_top_of_subset hZ hfinite
  have hZnonneg : 0 ≤ μ.real Z := measureReal_nonneg
  have hradius := radius_pos J j
  refine ⟨j,hj,x,hY.inter measurableSet_closedBall,hmass,?_⟩
  intro y r hbottom hr
  change μ.real (Z ∩ Metric.closedBall y r) ≤ _
  have hrpos : 0 < r := (radius_pos J 0).trans_le hbottom
  have htrivial : μ.real (Z ∩ Metric.closedBall y r) ≤ μ.real Z :=
    measureReal_mono Set.inter_subset_left hZfinite
  have hid : (2 : ℝ)^alpha * (r / radius J j)^alpha =
      (2*r / radius J j)^alpha := by
    rw [← Real.mul_rpow (by norm_num) (div_nonneg hrpos.le hradius.le)]
    congr 1
    ring
  rw [hid]
  by_cases hlarge : radius J j ≤ 2*r
  · have hone : (1 : ℝ) ≤ (2*r / radius J j)^alpha := by
      have hratio : (1 : ℝ) ≤ 2*r / radius J j :=
        (le_div_iff₀ hradius).mpr (by simpa using hlarge)
      simpa using Real.rpow_le_rpow (by norm_num : (0:ℝ) ≤ 1) hratio ha
    exact htrivial.trans (by nlinarith)
  · have hsmall : 2*r < radius J j := lt_of_not_ge hlarge
    have hrtop : r ≤ 1 := hr.trans (by simpa using radius_mono J hj)
    obtain ⟨i,hi,hri,hir⟩ := dyadic_round hbottom hrtop
    have hij : i < j := by
      by_contra hh
      have := radius_mono J (Nat.le_of_not_gt hh)
      linarith
    have hfail := Nat.find_min hex hij
    have hupper : μ.real (Y ∩ Metric.closedBall y (radius J i)) <
        (radius J i)^alpha * μ.real Y := by
      exact lt_of_not_ge (fun h => hfail ⟨hi,y,h⟩)
    have hrestrict : μ.real (Z ∩ Metric.closedBall y r) ≤
        μ.real (Y ∩ Metric.closedBall y (radius J i)) :=
      measureReal_mono (Set.inter_subset_inter hZ (Metric.closedBall_subset_closedBall hri))
        (measure_ne_top_of_subset Set.inter_subset_left hfinite)
    have hscale : (radius J i)^alpha ≤ (2*r)^alpha :=
      Real.rpow_le_rpow (radius_pos J i).le hir ha
    have hstep : μ.real (Z ∩ Metric.closedBall y r) ≤ (2*r)^alpha * μ.real Y :=
      hrestrict.trans (hupper.le.trans (mul_le_mul_of_nonneg_right hscale measureReal_nonneg))
    have hdenom : 0 < (radius J j)^alpha := Real.rpow_pos_of_pos hradius _
    have hmdiv : μ.real Y ≤ μ.real Z / (radius J j)^alpha :=
      (le_div_iff₀ hdenom).mpr (by simpa only [Z,j,mul_comm] using hmass)
    have hh := mul_le_mul_of_nonneg_left hmdiv
      (Real.rpow_nonneg (by positivity : 0 ≤ 2*r) alpha)
    rw [Real.div_rpow (by positivity : 0 ≤ 2*r) hradius.le]
    exact hstep.trans (by simpa only [div_eq_mul_inv,mul_assoc,mul_left_comm,mul_comm] using hh)

end KakeyaFormal.MeasurableLocalization
