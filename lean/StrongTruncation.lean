import RestrictedInterpolation
import Mathlib.MeasureTheory.Integral.Lebesgue.Markov

/-! Actual high/low input truncation and the resulting two-endpoint level
estimate. Endpoint estimates are applied to the constructed measurable inputs. -/
namespace KakeyaFormal.StrongTruncation
open MeasureTheory Set RestrictedInterpolation
open scoped ENNReal
noncomputable section
open Classical

def high {X : Type*} (f : X → ℝ≥0∞) (s : ℝ≥0∞) : X → ℝ≥0∞ :=
  {x | s < f x}.indicator f

def low {X : Type*} (f : X → ℝ≥0∞) (s : ℝ≥0∞) : X → ℝ≥0∞ :=
  {x | f x ≤ s}.indicator f

theorem high_measurable {X : Type*} [MeasurableSpace X] {f : X → ℝ≥0∞}
    (hf : Measurable f) (s : ℝ≥0∞) : Measurable (high f s) :=
  hf.indicator (measurableSet_lt measurable_const hf)

theorem low_measurable {X : Type*} [MeasurableSpace X] {f : X → ℝ≥0∞}
    (hf : Measurable f) (s : ℝ≥0∞) : Measurable (low f s) :=
  hf.indicator (measurableSet_le hf measurable_const)

theorem partition {X : Type*} (f : X → ℝ≥0∞) (s : ℝ≥0∞) :
    f = high f s + low f s := by
  funext x
  by_cases h : s < f x
  · simp [high,low,h,not_le.mpr h]
  · simp [high,low,h,le_of_not_gt h]

theorem level_cover {X Y : Type*} [MeasurableSpace X]
    {T : (X → ℝ≥0∞) → Y → ℝ≥0∞} (hT : PositiveLaws T)
    {f : X → ℝ≥0∞} (hf : Measurable f) (s : ℝ≥0∞)
    {t : ℝ} (ht : 0 < t) :
    {y | ENNReal.ofReal t < T f y} ⊆
      {y | ENNReal.ofReal (t/2) < T (high f s) y} ∪
      {y | ENNReal.ofReal (t/2) < T (low f s) y} := by
  intro y hy
  by_contra h
  have hhi : T (high f s) y ≤ ENNReal.ofReal (t/2) := by
    exact le_of_not_gt (fun hhi => h (Or.inl hhi))
  have hlo : T (low f s) y ≤ ENNReal.ofReal (t/2) := by
    exact le_of_not_gt (fun hlo => h (Or.inr hlo))
  have hsum := hT.add_le (high f s) (low f s) (high_measurable hf s) (low_measurable hf s) y
  rw [← partition] at hsum
  have heq : ENNReal.ofReal (t/2) + ENNReal.ofReal (t/2) = ENNReal.ofReal t := by
    rw [← ENNReal.ofReal_add (by positivity) (by positivity)]
    congr 1
    ring
  exact (not_lt_of_ge (hsum.trans ((add_le_add hhi hlo).trans_eq heq))) hy

theorem power_markov {Y : Type*} [MeasurableSpace Y] (ν : Measure Y)
    {g : Y → ℝ≥0∞} (hg : Measurable g) {t p : ℝ} (ht : 0 < t) (hp : 0 < p) :
    ν {y | ENNReal.ofReal t < g y} ≤
      (∫⁻ y, g y ^ p ∂ν) / ENNReal.ofReal (t ^ p) := by
  have heq : ENNReal.ofReal (t^p) = (ENNReal.ofReal t)^p :=
    (ENNReal.ofReal_rpow_of_pos ht).symm
  apply (measure_mono (fun y hy => ?_)).trans
    (meas_ge_le_lintegral_div (hg.pow_const p).aemeasurable
      (ENNReal.ofReal_pos.mpr (Real.rpow_pos_of_pos ht p)).ne' ENNReal.ofReal_ne_top)
  change ENNReal.ofReal (t^p) ≤ g y^p
  rw [heq]
  exact (ENNReal.rpow_lt_rpow hy hp).le

/-- The two strong endpoint bounds imply a level bound for the literal
constructed truncations, without assuming either truncation belongs to an Lp space. -/
theorem level_bound {X Y : Type*} [MeasurableSpace X] [MeasurableSpace Y]
    (μ : Measure X) (ν : Measure Y) {T : (X → ℝ≥0∞) → Y → ℝ≥0∞}
    (hT : PositiveLaws T) (hmeas : ∀ f, Measurable f → Measurable (T f))
    {r A₁ B : ℝ} (hr : 0 < r)
    (h₁ : ∀ f, Measurable f → (∫⁻ y, T f y ∂ν) ≤ ENNReal.ofReal A₁ * ∫⁻ x, f x ∂μ)
    (hᵣ : ∀ f, Measurable f → (∫⁻ y, T f y ^ r ∂ν) ≤ ENNReal.ofReal B * ∫⁻ x, f x ^ r ∂μ)
    {f : X → ℝ≥0∞} (hf : Measurable f) (s : ℝ≥0∞) {t : ℝ} (ht : 0 < t) :
    ν {y | ENNReal.ofReal t < T f y} ≤
      (ENNReal.ofReal A₁ * ∫⁻ x, high f s x ∂μ) / ENNReal.ofReal (t/2) +
      (ENNReal.ofReal B * ∫⁻ x, low f s x ^ r ∂μ) / ENNReal.ofReal ((t/2)^r) := by
  have hhi := high_measurable hf s
  have hlo := low_measurable hf s
  apply (measure_mono (level_cover hT hf s ht)).trans
    ((measure_union_le _ _).trans ?_)
  apply add_le_add
  · have h := power_markov ν (hmeas _ hhi) (show 0 < t/2 by positivity) (show (0:ℝ)<1 by norm_num)
    simp only [Real.rpow_one,ENNReal.rpow_one] at h
    exact h.trans (ENNReal.div_le_div_right (h₁ _ hhi) _)
  · exact (power_markov ν (hmeas _ hlo) (show 0 < t/2 by positivity) hr).trans
      (ENNReal.div_le_div_right (hᵣ _ hlo) _)

end
end KakeyaFormal.StrongTruncation
