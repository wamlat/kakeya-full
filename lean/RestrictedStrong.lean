import DyadicStrong
import DyadicOperatorExtension
import RestrictedOperatorLaws
import OperatorRestrictedWeak

/-! Actual first-stage strong interpolation for the Kakeya operator. The
restricted indicator estimate is combined with the proved dyadic moment theorem
and the actual monotone extension. All constants precede the mesh and input. -/
namespace KakeyaFormal.RestrictedStrong
open MeasureTheory Set Finset KakeyaOperator RestrictedInterpolation
open scoped ENNReal NNReal
noncomputable section

def gamma (a r : ℝ) : ℝ := (r-a)/(2*a)

def coefficient (a r : ℝ) : ℝ :=
  (2:ℝ)^(2*r)*r*(1-(decayRatio (gamma a r):ℝ))^(-a)/(r-a*(1+gamma a r))

theorem gamma_tests {a r : ℝ} (ha : 0 < a) (har : a < r) :
    0 < gamma a r ∧ a*(1+gamma a r) < r := by
  have hgamma : 0 < gamma a r := div_pos (sub_pos.mpr har) (by positivity)
  have heq : a*(1+gamma a r) = (a+r)/2 := by
    dsimp [gamma]
    field_simp
    ring
  exact ⟨hgamma,by rw [heq]; linarith⟩

theorem coefficient_pos {a r : ℝ} (ha : 0 < a) (har : a < r) :
    0 < coefficient a r := by
  have ht := gamma_tests ha har
  have hdecay : 0 < 1-(decayRatio (gamma a r):ℝ) :=
    sub_pos.mpr (decayRatio_lt_one ht.1)
  have hr : 0 < r := ha.trans har
  unfold coefficient
  exact div_pos (by positivity) (sub_pos.mpr ht.2)

/-- The two independent factors 2^r are the finite level split and the
actual dyadic approximation; both are included in the fixed real constant. -/
theorem coefficient_identity {a r A : ℝ} (ha : 0 < a) (har : a < r) :
    (2:ℝ≥0∞)^r * ((2:ℝ≥0∞)^r * ENNReal.ofReal r *
      ENNReal.ofReal ((A*(1-(decayRatio (gamma a r):ℝ))^(-a))/(r-a*(1+gamma a r)))) =
        ENNReal.ofReal (coefficient a r*A) := by
  have ht := gamma_tests ha har
  have hr : 0 < r := ha.trans har
  have hdecay : 0 < 1-(decayRatio (gamma a r):ℝ) :=
    sub_pos.mpr (decayRatio_lt_one ht.1)
  have hid : coefficient a r*A =
      ((2:ℝ)^r*(2:ℝ)^r*r)*((A*(1-(decayRatio (gamma a r):ℝ))^(-a))/(r-a*(1+gamma a r))) := by
    unfold coefficient
    rw [show 2*r=r+r by ring,Real.rpow_add (by norm_num : (0:ℝ)<2)]
    ring
  rw [hid,ENNReal.ofReal_mul (by positivity),ENNReal.ofReal_mul (by positivity),
    ENNReal.ofReal_mul (by positivity)]
  simp only [← ENNReal.ofReal_rpow_of_pos (by norm_num : (0:ℝ)<2),ENNReal.ofReal_ofNat]
  ring

/-- Actual indicator weak type at exponent a gives actual strong rth moments
for each r>a. Every operator law and every output measurability requirement is
discharged by the literal Kakeya operator. -/
theorem from_restricted_weak {k : ℕ} {a r : ℝ} (ha : 0 < a) (har : a < r)
    {δ A : ℝ} (hδ : 0 < δ) (hA : 0 ≤ A)
    (hweak : ∀ E : Set (Space (k+1)), MeasurableSet E → ∀ u : ℝ, 0 < u →
      (sphereMeasure (k+1)) {v : Direction (k+1) |
        ENNReal.ofReal u < maximal δ (E.indicator (fun _ => 1)) v} ≤
          ENNReal.ofReal (A*u^(-a))*(volume : Measure (Space (k+1))) E)
    (f : Space (k+1) → ℝ≥0∞) (hf : Measurable f) :
    (∫⁻ v, maximal δ f v ^ r ∂sphereMeasure (k+1)) ≤
      ENNReal.ofReal (coefficient a r*A)*(∫⁻ x, f x ^ r ∂volume) := by
  have ht := gamma_tests ha har
  let B : ℝ≥0∞ := (2:ℝ≥0∞)^r * ENNReal.ofReal r *
    ENNReal.ofReal ((A*(1-(decayRatio (gamma a r):ℝ))^(-a))/(r-a*(1+gamma a r)))
  have hfinite : DyadicOperatorExtension.FiniteMomentBound k δ r B := by
    intro s E hE hdisj
    exact dyadic_strong_moment (volume : Measure (Space (k+1))) (sphereMeasure (k+1))
      (RestrictedOperatorLaws.positive_laws hδ) s E hE hdisj
      (KakeyaOperatorMeasurability.maximal_measurable hδ _ (bandSum_measurable s dyadicHeight E hE))
      ht.1 ha hA ht.2 (fun j hj u hu => hweak (E j) (hE j hj) u hu)
  have hh := DyadicOperatorExtension.extend hδ (ha.trans har) hfinite f hf
  have hcoef : (2:ℝ≥0∞)^r*B = ENNReal.ofReal (coefficient a r*A) :=
    coefficient_identity ha har
  rwa [hcoef] at hh

/-- Complete first-stage scale bound, with its positive constant chosen before
all meshes and measurable inputs, including inputs of infinite integral. -/
theorem from_estimate {k : ℕ} {a r : ℝ}
    (hestimate : OperatorRestrictedWeak.Estimate (k+1) a) (ha : 0 < a) (har : a < r)
    {eps : ℝ} (heps : 0 < eps) :
    ∃ C : ℝ, 0 < C ∧ ∀ {δ : ℝ}, 0 < δ → δ ≤ 1 →
      ∀ f : Space (k+1) → ℝ≥0∞, Measurable f →
        (∫⁻ v, maximal δ f v ^ r ∂sphereMeasure (k+1)) ≤
          ENNReal.ofReal (C*δ^(-(((k+1:ℕ):ℝ)-a+eps)))*
            (∫⁻ x, f x ^ r ∂volume) := by
  obtain ⟨A,hA,hweak⟩ := hestimate eps heps
  refine ⟨coefficient a r*A,mul_pos (coefficient_pos ha har) hA,?_⟩
  intro δ hδ hδ1 f hf
  have hAδ : 0 ≤ A*δ^(-(((k+1:ℕ):ℝ)-a+eps)) := by positivity
  have hh := from_restricted_weak ha har hδ hAδ (hweak hδ hδ1) f hf
  simpa only [mul_assoc] using hh

end
end KakeyaFormal.RestrictedStrong
