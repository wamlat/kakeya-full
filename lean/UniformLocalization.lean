import MeasurableLocalization
import ScaleChoice

/-! Smallest-scale localization for an arbitrary real mesh scale δ, with a
logarithmic bound on the number of dyadic scales and all-radii two ends. -/
namespace KakeyaFormal.UniformLocalization
open KakeyaFormal.Localization
open MeasureTheory Set
open scoped ENNReal

/-- Moving the bottom test scale upward by at most two only changes 2^α to 4^α. -/
theorem extend_two_ends {f : ℝ → ℝ} (hmono : Monotone f)
    {δ bottom rho alpha M : ℝ} (hδ : 0 < δ) (hbottom : bottom ≤ 2*δ)
    (hbρ : bottom ≤ rho) (hρ : 0 < rho) (ha : 0 ≤ alpha) (hM : 0 ≤ M)
    (hbound : ∀ r : ℝ, bottom ≤ r → r ≤ rho →
      f r ≤ (2:ℝ)^alpha*(r/rho)^alpha*M)
    {r : ℝ} (hrδ : δ ≤ r) (hrρ : r ≤ rho) :
    f r ≤ (4:ℝ)^alpha*(r/rho)^alpha*M := by
  let R := max r bottom
  have hRlo : bottom ≤ R := le_max_right _ _
  have hRhi : R ≤ rho := max_le hrρ hbρ
  have hrpos : 0 < r := hδ.trans_le hrδ
  have hRpos : 0 < R := hrpos.trans_le (le_max_left _ _)
  have hR2 : R ≤ 2*r := max_le (by linarith) (by linarith)
  have hleft : (2:ℝ)^alpha*(R/rho)^alpha = (2*R/rho)^alpha := by
    rw [← Real.mul_rpow (by norm_num) (div_nonneg hRpos.le hρ.le)]
    congr 1
    ring
  have hright : (4:ℝ)^alpha*(r/rho)^alpha = (4*r/rho)^alpha := by
    rw [← Real.mul_rpow (by norm_num) (div_nonneg hrpos.le hρ.le)]
    congr 1
    ring
  have hscale : (2*R/rho)^alpha ≤ (4*r/rho)^alpha :=
    Real.rpow_le_rpow (by positivity) (div_le_div_of_nonneg_right (by linarith) hρ.le) ha
  have hh := (hmono (le_max_left r bottom)).trans (hbound R hRlo hRhi)
  rw [hleft] at hh
  rw [hright]
  exact hh.trans (mul_le_mul_of_nonneg_right hscale hM)

/-- Finite weighted localization at every real mesh scale, with a finite
logarithmic depth and no assumption of a preselected good restriction. -/
theorem finite_localization {X : Type*} [MetricSpace X]
    (s : Finset X) (w : X → ℝ) (hw : ∀ x, 0 ≤ w x)
    {δ alpha : ℝ} (hδ : 0 < δ) (hδ1 : δ ≤ 1) (ha : 0 ≤ alpha)
    (x₀ : X) (hcover : ∀ y ∈ s, dist y x₀ ≤ 1) :
    ∃ J j : ℕ, ∃ x : X, j ≤ J ∧
      (J:ℝ) ≤ Real.log (1/δ)/Real.log 2 ∧
      let rho := radius J j
      let Z := restrict s x rho
      δ ≤ rho ∧ rho ≤ 1 ∧ rho^alpha*mass w s ≤ mass w Z ∧
      ∀ y : X, ∀ r : ℝ, δ ≤ r → r ≤ rho →
        mass w (restrict Z y r) ≤ (4:ℝ)^alpha*(r/rho)^alpha*mass w Z := by
  obtain ⟨J,hbottom,hbottom2,hdepth⟩ := ScaleChoice.dyadic_depth hδ hδ1
  obtain ⟨j,hj,x,hmass,hends⟩ := smallest_scale_two_ends s w hw J ha x₀ hcover
  have hbr := radius_mono J (Nat.zero_le j)
  refine ⟨J,j,x,hj,hdepth,hbottom.trans hbr,?_,hmass,?_⟩
  · simpa only [radius_top] using radius_mono J hj
  · intro y r hr hrρ
    apply extend_two_ends (f := fun r => mass w (restrict (restrict s x (radius J j)) y r))
      (fun a b hab => mass_mono hw (restrict_mono (by rfl) y hab))
      hδ hbottom2.le hbr (radius_pos J j) ha (mass_nonneg hw _) (hends y) hr hrρ

/-- Measurable version for finite shadings in an arbitrary metric Borel space.
The ambient measure may be infinite, as with Euclidean Lebesgue measure. -/
theorem measurable_localization {X : Type*} [MetricSpace X]
    [MeasurableSpace X] [BorelSpace X] (μ : Measure X) (Y : Set X)
    (hY : MeasurableSet Y) (hfinite : μ Y ≠ ∞)
    {δ alpha : ℝ} (hδ : 0 < δ) (hδ1 : δ ≤ 1) (ha : 0 ≤ alpha)
    (x₀ : X) (hcover : Y ⊆ Metric.closedBall x₀ 1) :
    ∃ J j : ℕ, ∃ x : X, j ≤ J ∧
      (J:ℝ) ≤ Real.log (1/δ)/Real.log 2 ∧
      let rho := radius J j
      let Z := Y ∩ Metric.closedBall x rho
      δ ≤ rho ∧ rho ≤ 1 ∧ MeasurableSet Z ∧ rho^alpha*μ.real Y ≤ μ.real Z ∧
      ∀ y : X, ∀ r : ℝ, δ ≤ r → r ≤ rho →
        μ.real (Z ∩ Metric.closedBall y r) ≤ (4:ℝ)^alpha*(r/rho)^alpha*μ.real Z := by
  obtain ⟨J,hbottom,hbottom2,hdepth⟩ := ScaleChoice.dyadic_depth hδ hδ1
  obtain ⟨j,hj,x,hZ,hmass,hends⟩ :=
    MeasurableLocalization.smallest_scale_two_ends μ Y hY hfinite J ha x₀ hcover
  have hbr := radius_mono J (Nat.zero_le j)
  refine ⟨J,j,x,hj,hdepth,hbottom.trans hbr,?_,hZ,hmass,?_⟩
  · simpa only [radius_top] using radius_mono J hj
  · intro y r hr hrρ
    apply extend_two_ends
      (f := fun r => μ.real ((Y ∩ Metric.closedBall x (radius J j)) ∩ Metric.closedBall y r))
      (fun a b hab => measureReal_mono
        (Set.inter_subset_inter_right _ (Metric.closedBall_subset_closedBall hab))
        (measure_ne_top_of_subset (Set.inter_subset_left.trans Set.inter_subset_left) hfinite))
      hδ hbottom2.le hbr (radius_pos J j) ha measureReal_nonneg (hends y) hr hrρ

end KakeyaFormal.UniformLocalization
