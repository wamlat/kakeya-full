import DyadicApproximation
import KakeyaOperatorMeasurability

/-! Monotone extension from genuine finite dyadic inputs to every measurable
input for the actual Kakeya operator. Only the finite-stage moment estimate is
an analytic premise; all operator laws, measurability and approximations are
proved for the literal original-position operator. -/
namespace KakeyaFormal.DyadicOperatorExtension
open MeasureTheory Set Finset KakeyaOperator DyadicApproximation RestrictedInterpolation
open scoped ENNReal NNReal
noncomputable section

/-- The precise finite-stage estimate to be discharged by dyadic restricted
weak interpolation. Its inputs are actual measurable pairwise disjoint sets. -/
def FiniteMomentBound (k : ℕ) (δ r : ℝ) (B : ℝ≥0∞) : Prop :=
  ∀ s : Finset ℤ, ∀ E : ℤ → Set (Space (k+1)),
    (∀ j ∈ s, MeasurableSet (E j)) →
    (↑s : Set ℤ).Pairwise (fun i j => Disjoint (E i) (E j)) →
    (∫⁻ v, maximal δ (bandSum s dyadicHeight E) v ^ r ∂sphereMeasure (k+1)) ≤
      B * (∫⁻ x, bandSum s dyadicHeight E x ^ r ∂volume)

/-- The actual operator sees the pointwise dyadic approximation with at most
its fixed factor-two loss. The supremum ranges over every actual tube base. -/
theorem maximal_le_two_iSup {k : ℕ} (δ : ℝ) (f : Space (k+1) → ℝ≥0∞)
    (hf : Measurable f) (v : Direction (k+1)) :
    maximal δ f v ≤ 2*(⨆ N, maximal δ (approx f N) v) := by
  have hh := KakeyaOperatorLaws.maximal_mono δ (le_two_iSup_approx f) v
  rw [KakeyaOperatorLaws.maximal_finite_mul δ 2 (by norm_num),
    KakeyaOperatorLaws.maximal_iSup δ (approx f) (approx_measurable hf) (approx_mono f)] at hh
  exact hh

theorem rpow_iSup {ι : Type*} (g : ι → ℝ≥0∞) {r : ℝ} (hr : 0 < r) :
    (⨆ i, g i)^r = ⨆ i, (g i)^r :=
  (ENNReal.orderIsoRpow r hr).map_iSup g

/-- Actual finite-stage bounds imply the full measurable input bound with
only the explicit factor 2^r. Infinite input values and infinite integrals are
allowed, with no separate a.e.-finiteness assumption. -/
theorem extend {k : ℕ} {δ r : ℝ} (hδ : 0 < δ) (hr : 0 < r)
    {B : ℝ≥0∞} (hfinite : FiniteMomentBound k δ r B)
    (f : Space (k+1) → ℝ≥0∞) (hf : Measurable f) :
    (∫⁻ v, maximal δ f v ^ r ∂sphereMeasure (k+1)) ≤
      (2:ℝ≥0∞)^r * B * (∫⁻ x, f x ^ r ∂volume) := by
  let g : ℕ → Direction (k+1) → ℝ≥0∞ := fun N v => maximal δ (approx f N) v ^ r
  have hg : ∀ N, Measurable (g N) := fun N =>
    ENNReal.continuous_rpow_const.measurable.comp
      (KakeyaOperatorMeasurability.maximal_measurable hδ _ (approx_measurable hf N))
  have hgmono : Monotone g := by
    intro N M hNM v
    exact ENNReal.rpow_le_rpow (KakeyaOperatorLaws.maximal_mono δ (approx_mono f hNM) v) hr.le
  have hN (N : ℕ) : (∫⁻ v, g N v ∂sphereMeasure (k+1)) ≤
      B*(∫⁻ x, f x ^ r ∂volume) := by
    have hb := hfinite (indices N) (bands f N) (fun j _ => bands_measurable hf N j)
      (bands_disjoint f N)
    exact hb.trans (mul_le_mul' le_rfl
      (lintegral_mono (fun x => ENNReal.rpow_le_rpow (approx_le f N x) hr.le)))
  have hpoint (v : Direction (k+1)) :
      maximal δ f v ^ r ≤ (2:ℝ≥0∞)^r * (⨆ N, g N v) := by
    have hh := ENNReal.rpow_le_rpow (maximal_le_two_iSup δ f hf v) hr.le
    rw [ENNReal.mul_rpow_of_nonneg _ _ hr.le,rpow_iSup _ hr] at hh
    exact hh
  calc
    _ ≤ ∫⁻ v, (2:ℝ≥0∞)^r * (⨆ N, g N v) ∂sphereMeasure (k+1) := lintegral_mono hpoint
    _ = (2:ℝ≥0∞)^r * (∫⁻ v, (⨆ N, g N v) ∂sphereMeasure (k+1)) :=
      lintegral_const_mul _ (Measurable.iSup hg)
    _ = (2:ℝ≥0∞)^r * (⨆ N, ∫⁻ v, g N v ∂sphereMeasure (k+1)) := by
      rw [lintegral_iSup hg hgmono]
    _ ≤ (2:ℝ≥0∞)^r * (B*(∫⁻ x, f x ^ r ∂volume)) :=
      mul_le_mul' le_rfl (iSup_le hN)
    _ = _ := (mul_assoc _ _ _).symm

end
end KakeyaFormal.DyadicOperatorExtension
