import MainEndpoint
import SixDimensionalUnrestricted
import DiagonalWeakening
import MaximalPositionReduction

/-! Literal measurable maximal assertions with arbitrary tube positions.
The actual spatial partition/translation reduction removes the bounded-base
convention. No cap coefficient, two ends, broadness, sampling, or unpublished
analytic result is supplied as a premise to the main results below. -/
namespace KakeyaFormal.MainMaximal
noncomputable section

/-- A proved diagonal grid estimate yields the literal maximal-shading
formula through the actual measurable, ambient-cap, and spatial adapters. -/
theorem from_diagonal {k : ℕ} {d : ℝ}
    (h : DiagonalDiscreteEstimate (k+1) d) (hd : 1 ≤ d) :
    MaximalShading.Estimate (k+1) d := by
  have h' : DiscreteEstimate (k+1) (k:ℝ) d d := by
    simpa only [DiagonalDiscreteEstimate,Nat.cast_add,Nat.cast_one,add_sub_cancel_right] using h
  exact MaximalPositionReduction.bounded_to_unbounded
    (MaximalShading.bounded_maximal_of_volume
      (h'.to_measurable_volume (by omega) hd le_rfl))

/-- The manuscript's main maximal assertion in every integer dimension n≥6,
with the exact algebraic endpoint and no restriction on tube positions. -/
theorem endpoint {n : ℕ} (hn : 6 ≤ n) :
    MaximalShading.Estimate n (KakeyaScalar.limitProfile ((n:ℝ)-1)) :=
  MaximalPositionReduction.bounded_to_unbounded (MainEndpoint.bounded_maximal hn)

/-- The explicit formula D_n=3+(2−sqrt2)(n−4), with the same literal
position-unrestricted measurable maximal predicate. -/
theorem endpoint_formula {n : ℕ} (hn : 6 ≤ n) :
    MaximalShading.Estimate n (3+(2-Real.sqrt 2)*((n:ℝ)-4)) := by
  have hid : KakeyaScalar.limitProfile ((n:ℝ)-1) = 3+(2-Real.sqrt 2)*((n:ℝ)-4) := by
    dsimp [KakeyaScalar.limitProfile,KakeyaScalar.slopeLimit]
    ring
  rw [← hid]
  exact endpoint hn

/-- The literal six-dimensional first improved exponent33/8. The base and
lifted fractional seeds are already proved; no M6(4) premise is needed. -/
theorem six_first : MaximalShading.Estimate 6 (33/8) :=
  MaximalPositionReduction.bounded_to_unbounded SixDimensionalUnrestricted.bounded_maximal

/-- The exact implication M6(4)→M6(33/8) in the manuscript's measurable,
cap-free, arbitrary-position predicate. Its conclusion is also unconditional. -/
theorem six_first_step (_base : MaximalShading.Estimate 6 4) :
    MaximalShading.Estimate 6 (33/8) := six_first

/-- The exact six-dimensional algebraic limit7−2sqrt2. -/
theorem six_endpoint : MaximalShading.Estimate 6 (7-2*Real.sqrt 2) :=
  MaximalPositionReduction.bounded_to_unbounded MainEndpoint.six_bounded_maximal

/-- The exact eight-dimensional algebraic limit11−4sqrt2. -/
theorem eight_endpoint : MaximalShading.Estimate 8 (11-4*Real.sqrt 2) :=
  MaximalPositionReduction.bounded_to_unbounded MainEndpoint.eight_bounded_maximal

/-- The recorded six-dimensional diagonal limit29/7. The simultaneous
set/density weakening is the proved integer-shading argument, followed by
the actual measurable conversion; density powers alone are not substituted. -/
theorem six_diagonal_limit : MaximalShading.Estimate 6 (29/7) :=
  from_diagonal (k:=5) DiagonalConsequences.six (by norm_num)

/-- The recorded eight-dimensional diagonal limit37/7. -/
theorem eight_diagonal_limit : MaximalShading.Estimate 8 (37/7) :=
  from_diagonal (k:=7) DiagonalConsequences.eight (by norm_num)

end
end KakeyaFormal.MainMaximal
