import UniformLocalization
import OccupancySelection

/-! One common dyadic localization radius for a finite family, retaining any
specified weighted objective at the explicit logarithmic class loss. -/
namespace KakeyaFormal.FamilyLocalization
open KakeyaFormal.Localization KakeyaFormal.UniformLocalization
open MeasureTheory Set
open scoped BigOperators ENNReal

variable {I X : Type*} [Fintype I] [MetricSpace X]

/-- The radii are chosen from the same scale list for every input shading.
Taking a=1 retains cardinality; taking a=original mass retains incidence mass. -/
theorem finite_family_localization (s : I → Finset X) (w : X → ℝ)
    (hw : ∀ x, 0 ≤ w x) (a : I → ℝ)
    {δ alpha : ℝ} (hδ : 0 < δ) (hδ1 : δ ≤ 1) (ha : 0 ≤ alpha)
    (x₀ : I → X) (hcover : ∀ i, ∀ y ∈ s i, dist y (x₀ i) ≤ 1) :
    ∃ J j : ℕ, ∃ x : I → X, ∃ S : Finset I,
      j ≤ J ∧ (J:ℝ) ≤ Real.log (1/δ)/Real.log 2 ∧
      (∑ i, a i)/(J+1:ℕ) ≤ ∑ i ∈ S, a i ∧
      δ ≤ radius J j ∧ radius J j ≤ 1 ∧
      ∀ i ∈ S,
        let rho := radius J j
        let Z := restrict (s i) (x i) rho
        rho^alpha * mass w (s i) ≤ mass w Z ∧
        ∀ y : X, ∀ r : ℝ, δ ≤ r → r ≤ rho →
          mass w (restrict Z y r) ≤ (4:ℝ)^alpha*(r/rho)^alpha*mass w Z := by
  classical
  obtain ⟨J,hbottom,hbottom2,hdepth⟩ := ScaleChoice.dyadic_depth hδ hδ1
  choose j hj x hmass hends using fun i =>
    smallest_scale_two_ends (s i) w hw J ha (x₀ i) (hcover i)
  let label : I → Fin (J+1) := fun i => ⟨j i, by have := hj i; omega⟩
  obtain ⟨b,hb⟩ := OccupancySelection.weighted_class_selection Finset.univ a
    (Nat.succ_pos J) label
  let S := Finset.univ.filter (fun i => label i = b)
  have hbr := radius_mono J (Nat.zero_le b.val)
  refine ⟨J,b.val,x,S,by omega,hdepth,hb,hbottom.trans hbr,?_,?_⟩
  · simpa only [radius_top] using radius_mono J (show b.val ≤ J by omega)
  · intro i hi
    have hji : j i = b.val := congrArg Fin.val (Finset.mem_filter.mp hi).2
    rw [← hji]
    refine ⟨hmass i,?_⟩
    intro y r hr hrρ
    apply extend_two_ends (f := fun r => mass w (restrict (restrict (s i) (x i) (radius J (j i))) y r))
      (fun a b hab => mass_mono hw (restrict_mono (by rfl) y hab))
      hδ hbottom2.le (radius_mono J (Nat.zero_le (j i))) (radius_pos J (j i))
      ha (mass_nonneg hw _) (hends i y) hr hrρ

/-- Common-radius selection for actual measurable shadings, with every selected
shading retaining all-radii two ends and its quantitative original-mass fraction. -/
theorem measurable_family_localization [MeasurableSpace X] [BorelSpace X]
    (μ : Measure X) (Y : I → Set X) (hY : ∀ i, MeasurableSet (Y i))
    (hfinite : ∀ i, μ (Y i) ≠ ∞) (a : I → ℝ)
    {δ alpha : ℝ} (hδ : 0 < δ) (hδ1 : δ ≤ 1) (ha : 0 ≤ alpha)
    (x₀ : I → X) (hcover : ∀ i, Y i ⊆ Metric.closedBall (x₀ i) 1) :
    ∃ J j : ℕ, ∃ x : I → X, ∃ S : Finset I,
      j ≤ J ∧ (J:ℝ) ≤ Real.log (1/δ)/Real.log 2 ∧
      (∑ i, a i)/(J+1:ℕ) ≤ ∑ i ∈ S, a i ∧
      δ ≤ radius J j ∧ radius J j ≤ 1 ∧
      ∀ i ∈ S,
        let rho := radius J j
        let Z := Y i ∩ Metric.closedBall (x i) rho
        MeasurableSet Z ∧ rho^alpha * μ.real (Y i) ≤ μ.real Z ∧
        ∀ y : X, ∀ r : ℝ, δ ≤ r → r ≤ rho →
          μ.real (Z ∩ Metric.closedBall y r) ≤
            (4:ℝ)^alpha*(r/rho)^alpha*μ.real Z := by
  classical
  obtain ⟨J,hbottom,hbottom2,hdepth⟩ := ScaleChoice.dyadic_depth hδ hδ1
  choose j hj x hZ hmass hends using fun i =>
    MeasurableLocalization.smallest_scale_two_ends μ (Y i) (hY i) (hfinite i)
      J ha (x₀ i) (hcover i)
  let label : I → Fin (J+1) := fun i => ⟨j i, by have := hj i; omega⟩
  obtain ⟨b,hb⟩ := OccupancySelection.weighted_class_selection Finset.univ a
    (Nat.succ_pos J) label
  let S := Finset.univ.filter (fun i => label i = b)
  have hbr := radius_mono J (Nat.zero_le b.val)
  refine ⟨J,b.val,x,S,by omega,hdepth,hb,hbottom.trans hbr,?_,?_⟩
  · simpa only [radius_top] using radius_mono J (show b.val ≤ J by omega)
  · intro i hi
    have hji : j i = b.val := congrArg Fin.val (Finset.mem_filter.mp hi).2
    rw [← hji]
    refine ⟨hZ i, hmass i,?_⟩
    intro y r hr hrρ
    apply extend_two_ends
      (f := fun r => μ.real ((Y i ∩ Metric.closedBall (x i) (radius J (j i))) ∩ Metric.closedBall y r))
      (fun a b hab => measureReal_mono
        (Set.inter_subset_inter_right _ (Metric.closedBall_subset_closedBall hab))
        (measure_ne_top_of_subset (Set.inter_subset_left.trans Set.inter_subset_left) (hfinite i)))
      hδ hbottom2.le (radius_mono J (Nat.zero_le (j i))) (radius_pos J (j i))
      ha measureReal_nonneg (hends i y) hr hrρ

end KakeyaFormal.FamilyLocalization
