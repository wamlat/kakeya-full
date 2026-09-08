import IndicatorRestrictedWeak
import KakeyaOperatorLaws

/-! Restricted weak type for the actual original-position Kakeya operator.
The predicate concerns the extended-real operator on actual indicators. It
permits arbitrary measurable sets, including sets of infinite volume, and every
positive level. Its constant is uniform before scale, set, and level. -/
namespace KakeyaFormal.OperatorRestrictedWeak
open MeasureTheory Set KakeyaOperator
open scoped ENNReal
noncomputable section

/-- Actual indicator restricted weak type, with an arbitrary positive mesh
loss. No operator estimate is hidden behind a finite-net hypothesis. -/
def Estimate (n : ℕ) (a : ℝ) : Prop :=
  ∀ eps : ℝ, 0 < eps → ∃ C : ℝ, 0 < C ∧
    ∀ {δ : ℝ}, 0 < δ → δ ≤ 1 →
      ∀ E : Set (Space n), MeasurableSet E → ∀ lam : ℝ, 0 < lam →
        (sphereMeasure n) {v : Direction n |
          ENNReal.ofReal lam < maximal δ (E.indicator (fun _ => 1)) v} ≤
            ENNReal.ofReal (C*δ^(-((n:ℝ)-a+eps))*lam^(-a)) *
              (volume : Measure (Space n)) E

/-- The proved actual maximal-shading assertion supplies the actual operator
restricted weak estimate. Neither output measurability nor finite input volume
is required for this outer-measure inequality. -/
theorem from_shading {n : ℕ} {a : ℝ} (hn : 0 < n)
    (h : MaximalShading.Estimate n a) : Estimate n a := by
  intro eps heps
  obtain ⟨C,hC,hbound⟩ := IndicatorRestrictedWeak.real_bound hn h heps
  refine ⟨C,hC,?_⟩
  intro δ hδ hδ1 E hE lam hlam
  rw [KakeyaOperatorLaws.indicator_level_eq hδ hlam.le E hE]
  by_cases hlam1 : lam ≤ 1
  · have hcoef : 0 < C*δ^(-((n:ℝ)-a+eps))*lam^(-a) := by positivity
    by_cases hEfinite : (volume : Measure (Space n)) E ≠ ∞
    · have hh := ENNReal.ofReal_le_ofReal (hbound hδ hδ1 hlam hlam1 E hE hEfinite)
      rw [ENNReal.ofReal_mul hcoef.le] at hh
      simpa only [Measure.real,
        ENNReal.ofReal_toReal (SphereCapMeasure.sphere_finite _),
        ENNReal.ofReal_toReal hEfinite] using hh
    · have hEtop : (volume : Measure (Space n)) E = ∞ := not_ne_iff.mp hEfinite
      rw [hEtop,ENNReal.mul_top (ne_of_gt (ENNReal.ofReal_pos.mpr hcoef))]
      exact le_top
  · rw [indicatorLevel_empty hδ (le_of_not_ge hlam1),measure_empty]
    exact zero_le

/-- The concrete first improved six-dimensional exponent, for the actual
operator on all measurable indicators and at all positive levels. -/
theorem six_first : Estimate 6 (33/8) :=
  from_shading (by norm_num) MainMaximal.six_first

/-- The exact algebraic endpoint in each integer ambient dimension n≥6. -/
theorem endpoint {n : ℕ} (hn : 6 ≤ n) :
    Estimate n (KakeyaScalar.limitProfile ((n:ℝ)-1)) :=
  from_shading (by omega) (MainMaximal.endpoint hn)

/-- The explicit endpoint formula in the same actual operator predicate. -/
theorem endpoint_formula {n : ℕ} (hn : 6 ≤ n) :
    Estimate n (3+(2-Real.sqrt 2)*((n:ℝ)-4)) :=
  from_shading (by omega) (MainMaximal.endpoint_formula hn)

end
end KakeyaFormal.OperatorRestrictedWeak
