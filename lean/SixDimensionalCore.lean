import FractionalSeed
import MarkedPivotEstimate

/-! The actual six-dimensional marked pivot specialization. Both analytic
inputs are proved fractional seeds, so no published-result axiom is imported.
The resulting estimate retains its marked broadness, full two-ends, and fixed
logarithmic conditioning hypotheses. This is not an unrestricted M6 theorem. -/
namespace KakeyaFormal.SixDimensionalCore
open Finset
noncomputable section

/-- The actual six-dimensional base, with cap parameter five and both
exponents four. Uniform constants precede every geometric configuration. -/
theorem base : DiscreteEstimate 6 5 4 4 := by
  convert FractionalSeed.fractional_discrete_seed 4 (m:=5) (by norm_num) using 1 <;>
    norm_num

/-- The actual seven-dimensional lift, with cap parameter four and both
exponents seven halves. No projection or lower-dimensional estimate is assumed. -/
theorem lift : DiscreteEstimate 7 4 (7/2) (7/2) := by
  convert FractionalSeed.fractional_discrete_seed 5 (m:=4) (by norm_num) using 1 <;>
    norm_num

/-- Exact marked specialization D=33/8, C=15/4, hence 5-D=7/8.
The same actual full family and marked subsets occur in the hypothesis record.
The coefficient is fixed before scale, density, cap coefficient, population,
marked fraction, angular radius, and the actual geometric configuration. -/
theorem marked_estimate
    (width baseRadius : ℝ) (hw : (1:ℝ)/12 ≤ width)
    (eps : ℝ) (heps : 0 < eps)
    (B₀ K₀ xi₀ alpha bLog qLog xLog : ℝ)
    (hB₀ : 0 < B₀) (hK₀ : 0 < K₀) (hxi₀ : 0 < xi₀)
    (ha : 0 < alpha) (hb : 0 ≤ bLog) (hq : 0 ≤ qLog) (hx : 0 ≤ xLog) :
    ∃ c : ℝ, 0 < c ∧
      ∀ {M : ℕ} (F : TubeFamily 6 M) (E : Finset (Cell 6))
      (marks : Fin M → Finset (Cell 6)) {δ A lam xi B theta : ℝ},
      OriginalPivotSlabs.Hypotheses F E marks 1 δ A lam xi B theta
        width baseRadius 5 alpha B₀ K₀ bLog qLog →
      lam ≤ 1 → xi ≤ 1 → xi₀*(Real.log (2/δ))^(-xLog) ≤ xi →
      c*A⁻¹*δ^((7:ℝ)/8+eps)*lam^((15:ℝ)/4)*(M:ℝ) ≤ (E.card:ℝ) := by
  have h := MarkedPivotEstimate.all_scales (k:=4) base lift
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    width baseRadius hw eps heps B₀ K₀ xi₀ alpha bLog qLog xLog
    hB₀ hK₀ hxi₀ ha hb hq hx
  norm_num [KakeyaScalar.pivotSet,KakeyaScalar.pivotDensity] at h
  exact h

/-- Taking the covering set to be the actual full union gives a literal
occupied-cell lower bound, under the same visible marked/two-ends hypotheses. -/
theorem marked_union_estimate
    (width baseRadius : ℝ) (hw : (1:ℝ)/12 ≤ width)
    (eps : ℝ) (heps : 0 < eps)
    (B₀ K₀ xi₀ alpha bLog qLog xLog : ℝ)
    (hB₀ : 0 < B₀) (hK₀ : 0 < K₀) (hxi₀ : 0 < xi₀)
    (ha : 0 < alpha) (hb : 0 ≤ bLog) (hq : 0 ≤ qLog) (hx : 0 ≤ xLog) :
    ∃ c : ℝ, 0 < c ∧
      ∀ {M : ℕ} (F : TubeFamily 6 M)
      (marks : Fin M → Finset (Cell 6)) {δ A lam xi B theta : ℝ},
      OriginalPivotSlabs.Hypotheses F F.unionCells marks 1 δ A lam xi B theta
        width baseRadius 5 alpha B₀ K₀ bLog qLog →
      lam ≤ 1 → xi ≤ 1 → xi₀*(Real.log (2/δ))^(-xLog) ≤ xi →
      c*A⁻¹*δ^((7:ℝ)/8+eps)*lam^((15:ℝ)/4)*(M:ℝ) ≤ (F.unionCells.card:ℝ) := by
  obtain ⟨c,hc,hbound⟩ := marked_estimate width baseRadius hw eps heps
    B₀ K₀ xi₀ alpha bLog qLog xLog hB₀ hK₀ hxi₀ ha hb hq hx
  refine ⟨c,hc,?_⟩
  intro M F marks δ A lam xi B theta h hlam hxi hbudget
  exact hbound F F.unionCells marks h hlam hxi hbudget

end
end KakeyaFormal.SixDimensionalCore
