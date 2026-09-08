import ENNRealLayerCake
import TruncationIntegral

/-! Constructive interpolation between the strong L1 and Lr endpoints.
The proof uses actual input truncations, Markov, power layer cake and Tonelli.
No interpolation theorem or finite-integral assumption is supplied as an input. -/
namespace KakeyaFormal.StrongInterpolation
open MeasureTheory Set RestrictedInterpolation StrongTruncation TruncationIntegral
open scoped ENNReal
noncomputable section

def coefficient (a r A₁ B c : ℝ) : ℝ :=
  2*a*A₁*c^(1-a)/(a-1) + 2^r*a*B*c^(r-a)/(r-a)

theorem weighted_endpoint (U : ℝ≥0∞) {t a r B : ℝ} (ht : 0 < t) (hB : 0 ≤ B) :
    ((ENNReal.ofReal B*U)/ENNReal.ofReal ((t/2)^r))*ENNReal.ofReal (t^(a-1)) =
      ENNReal.ofReal (2^r*B)*(ENNReal.ofReal (t^(a-r-1))*U) := by
  have hc : ENNReal.ofReal B / ENNReal.ofReal ((t/2)^r) * ENNReal.ofReal (t^(a-1)) =
      ENNReal.ofReal (2^r*B) * ENNReal.ofReal (t^(a-r-1)) := by
    rw [← ENNReal.ofReal_div_of_pos (Real.rpow_pos_of_pos (by positivity : 0 < t/2) r),
      ← ENNReal.ofReal_mul (div_nonneg hB (Real.rpow_nonneg (by positivity : 0 ≤ t/2) r)),
      ← ENNReal.ofReal_mul (mul_nonneg (Real.rpow_nonneg (by norm_num) r) hB)]
    congr 1
    calc
      B/(t/2)^r*t^(a-1) = B*((t/2)^(-r)*t^(a-1)) := by
        rw [Real.rpow_neg (by positivity : 0 ≤ t/2)]
        ring
      _ = _ := by rw [cutoff_power_identity ht (by norm_num : (0:ℝ)<2)]; ring
  calc
    _ = (ENNReal.ofReal B / ENNReal.ofReal ((t/2)^r) * ENNReal.ofReal (t^(a-1)))*U := by
      simp only [div_eq_mul_inv]
      ring
    _ = _ := by rw [hc]; ring

theorem weighted_level_bound {X Y : Type*} [MeasurableSpace X] [MeasurableSpace Y]
    (μ : Measure X) (ν : Measure Y) {T : (X → ℝ≥0∞) → Y → ℝ≥0∞}
    (hT : PositiveLaws T) (hmeas : ∀ f, Measurable f → Measurable (T f))
    {a r A₁ B c : ℝ} (hr : 0 < r) (hA₁ : 0 ≤ A₁) (hB : 0 ≤ B)
    (h₁ : ∀ f, Measurable f → (∫⁻ y, T f y ∂ν) ≤ ENNReal.ofReal A₁ * ∫⁻ x, f x ∂μ)
    (hᵣ : ∀ f, Measurable f → (∫⁻ y, T f y ^ r ∂ν) ≤ ENNReal.ofReal B * ∫⁻ x, f x ^ r ∂μ)
    {f : X → ℝ≥0∞} (hf : Measurable f) {t : ℝ} (ht : 0 < t) :
    ν {y | ENNReal.ofReal t < T f y} * ENNReal.ofReal (t^(a-1)) ≤
      ENNReal.ofReal (2*A₁) * (ENNReal.ofReal (t^(a-2)) * ∫⁻ x, high f (ENNReal.ofReal (c*t)) x ∂μ) +
      ENNReal.ofReal (2^r*B) * (ENNReal.ofReal (t^(a-r-1)) * ∫⁻ x, low f (ENNReal.ofReal (c*t)) x^r ∂μ) := by
  have h := mul_le_mul' (level_bound μ ν hT hmeas hr h₁ hᵣ hf (ENNReal.ofReal (c*t)) ht)
    (le_rfl : ENNReal.ofReal (t^(a-1)) ≤ _)
  have hhi := weighted_endpoint (a:=a) (r:=1)
    (∫⁻ x, high f (ENNReal.ofReal (c*t)) x ∂μ) ht hA₁
  simp only [Real.rpow_one,show a-1-1 = a-2 by ring] at hhi
  rw [add_mul,hhi,weighted_endpoint _ ht hB] at h
  exact h

theorem coefficient_nonneg {a r A₁ B c : ℝ} (ha : 1 < a) (har : a < r)
    (hA₁ : 0 ≤ A₁) (hB : 0 ≤ B) (hc : 0 < c) : 0 ≤ coefficient a r A₁ B c := by
  dsimp [coefficient]
  positivity

/-- For arbitrary c>0, strong endpoint integral bounds imply the explicit
strong La integral bound, including infinite input/output values. -/
theorem strong_interpolation {X Y : Type*} [MeasurableSpace X] [MeasurableSpace Y]
    (μ : Measure X) [SFinite μ] (ν : Measure Y)
    {T : (X → ℝ≥0∞) → Y → ℝ≥0∞}
    (hT : PositiveLaws T) (hmeas : ∀ f, Measurable f → Measurable (T f))
    {a r A₁ B c : ℝ} (ha : 1 < a) (har : a < r)
    (hA₁ : 0 ≤ A₁) (hB : 0 ≤ B) (hc : 0 < c)
    (h₁ : ∀ f, Measurable f → (∫⁻ y, T f y ∂ν) ≤ ENNReal.ofReal A₁ * ∫⁻ x, f x ∂μ)
    (hᵣ : ∀ f, Measurable f → (∫⁻ y, T f y ^ r ∂ν) ≤ ENNReal.ofReal B * ∫⁻ x, f x ^ r ∂μ)
    {f : X → ℝ≥0∞} (hf : Measurable f) :
    (∫⁻ y, T f y^a ∂ν) ≤ ENNReal.ofReal (coefficient a r A₁ B c) * ∫⁻ x, f x^a ∂μ := by
  let H : ℝ → ℝ≥0∞ := fun t => ENNReal.ofReal (t^(a-2)) * ∫⁻ x, high f (ENNReal.ofReal (c*t)) x ∂μ
  let L : ℝ → ℝ≥0∞ := fun t => ENNReal.ofReal (t^(a-r-1)) * ∫⁻ x, low f (ENNReal.ofReal (c*t)) x^r ∂μ
  have hmH : Measurable H := by
    have h := (high_joint_measurable hf c a).lintegral_prod_right' (ν:=μ)
    simpa only [lintegral_const_mul' _ _ ENNReal.ofReal_ne_top] using h
  have hscalar : ENNReal.ofReal a *
      (ENNReal.ofReal (2*A₁)*ENNReal.ofReal (c^(1-a)/(a-1)) +
       ENNReal.ofReal (2^r*B)*ENNReal.ofReal (c^(r-a)/(r-a))) =
        ENNReal.ofReal (coefficient a r A₁ B c) := by
    rw [← ENNReal.ofReal_mul (by positivity : 0 ≤ 2*A₁),
      ← ENNReal.ofReal_mul (by positivity : 0 ≤ 2^r*B),
      ← ENNReal.ofReal_add (by positivity) (by positivity),
      ← ENNReal.ofReal_mul (by linarith : 0 ≤ a)]
    congr 1
    dsimp [coefficient]
    ring
  calc
    _ = ENNReal.ofReal a * ∫⁻ t in Ioi (0:ℝ),
        ν {y | ENNReal.ofReal t < T f y} * ENNReal.ofReal (t^(a-1)) :=
      ENNRealLayerCake.power_layercake ν (hmeas f hf) (by linarith)
    _ ≤ ENNReal.ofReal a * ∫⁻ t in Ioi (0:ℝ),
        ENNReal.ofReal (2*A₁)*H t + ENNReal.ofReal (2^r*B)*L t := by
      apply mul_le_mul' le_rfl
      apply lintegral_mono_ae
      filter_upwards [self_mem_ae_restrict measurableSet_Ioi] with t ht
      exact weighted_level_bound μ ν hT hmeas (by linarith) hA₁ hB h₁ hᵣ hf ht
    _ = ENNReal.ofReal a *
        (ENNReal.ofReal (2*A₁)*(∫⁻ t in Ioi (0:ℝ), H t) +
         ENNReal.ofReal (2^r*B)*(∫⁻ t in Ioi (0:ℝ), L t)) := by
      rw [lintegral_add_left (show Measurable (fun t => ENNReal.ofReal (2*A₁)*H t) from measurable_const.mul hmH)
          (fun t => ENNReal.ofReal (2^r*B)*L t),
        lintegral_const_mul' _ _ ENNReal.ofReal_ne_top,
        lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
    _ ≤ ENNReal.ofReal a *
        (ENNReal.ofReal (2*A₁)*(ENNReal.ofReal (c^(1-a)/(a-1))*(∫⁻ x, f x^a ∂μ)) +
         ENNReal.ofReal (2^r*B)*(ENNReal.ofReal (c^(r-a)/(r-a))*(∫⁻ x, f x^a ∂μ))) := by
      apply mul_le_mul' le_rfl
      exact add_le_add (mul_le_mul' le_rfl (high_integral_le μ hf hc ha))
        (mul_le_mul' le_rfl (low_integral_le μ hf hc ha har))
    _ = _ := by
      calc
        _ = (ENNReal.ofReal a *
            (ENNReal.ofReal (2*A₁)*ENNReal.ofReal (c^(1-a)/(a-1)) +
             ENNReal.ofReal (2^r*B)*ENNReal.ofReal (c^(r-a)/(r-a)))) * (∫⁻ x, f x^a ∂μ) := by ring
        _ = _ := by rw [hscalar]

end
end KakeyaFormal.StrongInterpolation
