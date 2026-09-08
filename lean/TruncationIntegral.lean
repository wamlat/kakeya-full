import TruncationKernels

/-! Nonnegative Tonelli integration of the actual truncations. Infinite
function values are included explicitly, without toReal on an unproved finite value. -/
namespace KakeyaFormal.TruncationIntegral
open MeasureTheory Set StrongTruncation TruncationKernels
open scoped ENNReal
noncomputable section
open Classical

theorem high_kernel_le (z : ℝ≥0∞) {c a : ℝ} (hc : 0 < c) (ha : 1 < a) :
    (∫⁻ t in Ioi (0:ℝ), ENNReal.ofReal (t^(a-2)) *
      high (fun _ : Unit => z) (ENNReal.ofReal (c*t)) ()) ≤
      ENNReal.ofReal (c^(1-a)/(a-1)) * z^a := by
  by_cases hz : z = ∞
  · rw [hz,ENNReal.top_rpow_of_pos (by linarith),ENNReal.mul_top (by
      exact (ENNReal.ofReal_pos.mpr (by positivity : 0 < c^(1-a)/(a-1))).ne')]
    exact le_top
  by_cases hz0 : z = 0
  · simp [hz0,high,show 0 < a by linarith]
  have hu := ENNReal.toReal_pos hz0 hz
  have h := (high_kernel_finite hu hc ha).le
  simpa only [ENNReal.ofReal_toReal hz] using h

theorem low_kernel_le (z : ℝ≥0∞) {c a r : ℝ} (hc : 0 < c) (ha : 1 < a) (har : a < r) :
    (∫⁻ t in Ioi (0:ℝ), ENNReal.ofReal (t^(a-r-1)) *
      low (fun _ : Unit => z) (ENNReal.ofReal (c*t)) () ^ r) ≤
      ENNReal.ofReal (c^(r-a)/(r-a)) * z^a := by
  by_cases hz : z = ∞
  · rw [hz,ENNReal.top_rpow_of_pos (by linarith),ENNReal.mul_top (by
      exact (ENNReal.ofReal_pos.mpr (by positivity : 0 < c^(r-a)/(r-a))).ne')]
    exact le_top
  by_cases hz0 : z = 0
  · simp [hz0,low,show 0 < a by linarith,show 0 < r by linarith]
  have hu := ENNReal.toReal_pos hz0 hz
  have h := (low_kernel_finite hu hc har (show 0 < r by linarith)).le
  simpa only [ENNReal.ofReal_toReal hz] using h

theorem high_joint_measurable {X : Type*} [MeasurableSpace X]
    {f : X → ℝ≥0∞} (hf : Measurable f) (c a : ℝ) :
    Measurable (fun p : ℝ × X => ENNReal.ofReal (p.1^(a-2)) * high f (ENNReal.ofReal (c*p.1)) p.2) := by
  have heq : (fun p : ℝ × X => ENNReal.ofReal (p.1^(a-2)) * high f (ENNReal.ofReal (c*p.1)) p.2) =
      {p | ENNReal.ofReal (c*p.1) < f p.2}.indicator
        (fun p => ENNReal.ofReal (p.1^(a-2)) * f p.2) := by
    funext p
    by_cases h : ENNReal.ofReal (c*p.1) < f p.2 <;> simp [high,h]
  rw [heq]
  exact ((by fun_prop : Measurable (fun p : ℝ × X => ENNReal.ofReal (p.1^(a-2)))).mul
    (hf.comp measurable_snd)).indicator (measurableSet_lt (by fun_prop) (hf.comp measurable_snd))

theorem low_joint_measurable {X : Type*} [MeasurableSpace X]
    {f : X → ℝ≥0∞} (hf : Measurable f) (c a : ℝ) {r : ℝ} (hr : 0 < r) :
    Measurable (fun p : ℝ × X => ENNReal.ofReal (p.1^(a-r-1)) * low f (ENNReal.ofReal (c*p.1)) p.2 ^ r) := by
  have heq : (fun p : ℝ × X => ENNReal.ofReal (p.1^(a-r-1)) * low f (ENNReal.ofReal (c*p.1)) p.2 ^ r) =
      {p | f p.2 ≤ ENNReal.ofReal (c*p.1)}.indicator
        (fun p => ENNReal.ofReal (p.1^(a-r-1)) * f p.2^r) := by
    funext p
    by_cases h : f p.2 ≤ ENNReal.ofReal (c*p.1) <;> simp [low,h,hr]
  rw [heq]
  exact ((by fun_prop : Measurable (fun p : ℝ × X => ENNReal.ofReal (p.1^(a-r-1)))).mul
    ((hf.comp measurable_snd).pow_const r)).indicator
      (measurableSet_le (hf.comp measurable_snd) (by fun_prop))

theorem high_integral_le {X : Type*} [MeasurableSpace X] (μ : Measure X) [SFinite μ]
    {f : X → ℝ≥0∞} (hf : Measurable f) {c a : ℝ} (hc : 0 < c) (ha : 1 < a) :
    (∫⁻ t in Ioi (0:ℝ), ENNReal.ofReal (t^(a-2)) *
      ∫⁻ x, high f (ENNReal.ofReal (c*t)) x ∂μ) ≤
      ENNReal.ofReal (c^(1-a)/(a-1)) * ∫⁻ x, f x^a ∂μ := by
  calc
    _ = ∫⁻ t in Ioi (0:ℝ), ∫⁻ x,
        ENNReal.ofReal (t^(a-2)) * high f (ENNReal.ofReal (c*t)) x ∂μ := by
      apply lintegral_congr
      intro t
      exact (lintegral_const_mul' _ _ ENNReal.ofReal_ne_top).symm
    _ = ∫⁻ x, (∫⁻ t in Ioi (0:ℝ),
        ENNReal.ofReal (t^(a-2)) * high f (ENNReal.ofReal (c*t)) x) ∂μ :=
      lintegral_lintegral_swap (high_joint_measurable hf c a).aemeasurable
    _ ≤ ∫⁻ x, ENNReal.ofReal (c^(1-a)/(a-1))*f x^a ∂μ :=
      lintegral_mono (fun x => high_kernel_le (f x) hc ha)
    _ = _ := lintegral_const_mul' _ _ ENNReal.ofReal_ne_top

theorem low_integral_le {X : Type*} [MeasurableSpace X] (μ : Measure X) [SFinite μ]
    {f : X → ℝ≥0∞} (hf : Measurable f) {c a r : ℝ} (hc : 0 < c) (ha : 1 < a) (har : a < r) :
    (∫⁻ t in Ioi (0:ℝ), ENNReal.ofReal (t^(a-r-1)) *
      ∫⁻ x, low f (ENNReal.ofReal (c*t)) x ^ r ∂μ) ≤
      ENNReal.ofReal (c^(r-a)/(r-a)) * ∫⁻ x, f x^a ∂μ := by
  calc
    _ = ∫⁻ t in Ioi (0:ℝ), ∫⁻ x,
        ENNReal.ofReal (t^(a-r-1)) * low f (ENNReal.ofReal (c*t)) x ^ r ∂μ := by
      apply lintegral_congr
      intro t
      exact (lintegral_const_mul' _ _ ENNReal.ofReal_ne_top).symm
    _ = ∫⁻ x, (∫⁻ t in Ioi (0:ℝ),
        ENNReal.ofReal (t^(a-r-1)) * low f (ENNReal.ofReal (c*t)) x ^ r) ∂μ :=
      lintegral_lintegral_swap (low_joint_measurable hf c a (show 0 < r by linarith)).aemeasurable
    _ ≤ ∫⁻ x, ENNReal.ofReal (c^(r-a)/(r-a))*f x^a ∂μ :=
      lintegral_mono (fun x => low_kernel_le (f x) hc ha har)
    _ = _ := lintegral_const_mul' _ _ ENNReal.ofReal_ne_top

end
end KakeyaFormal.TruncationIntegral
