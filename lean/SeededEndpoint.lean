import FractionalSeed
import Endpoint

/-! Top-level proof boundary after the actual fractional seed is established.
The endpoint and diagonal conclusions now assume only the still-unassembled
pivot estimate; the fractional seed is supplied by the proved theorem. -/
namespace KakeyaFormal.SeededEndpoint

/-- The exact real-cap endpoint, conditional only on the stated pivot estimate.
There is no supplied fractional-seed or two-ends premise. -/
theorem real_cap_endpoint_from_pivot
    (pivot : ∀ m d d' p q : ℝ,
      3 < d' → d' < d → d < m → d ≤ p → d' ≤ q →
      RealCapEstimate m d p → RealCapEstimate d d' q →
      RealCapEstimate m (KakeyaScalar.pivotSet m d')
        (max (KakeyaScalar.pivotSet m d') (KakeyaScalar.pivotDensity p q)))
    {m : ℝ} (hm : 3 < m) :
    RealCapEstimate m (KakeyaScalar.limitProfile m) (max (KakeyaScalar.limitProfile m) 4) :=
  real_cap_endpoint_from_seed_and_pivot (fun _ h => FractionalSeed.fractional_real_cap_seed h) pivot hm

/-- In every integer dimension n>=6 the exact diagonal endpoint assumes only
pivot. All seed construction and endpoint limiting arguments are checked. -/
theorem diagonal_endpoint_from_pivot
    (pivot : ∀ m d d' p q : ℝ,
      3 < d' → d' < d → d < m → d ≤ p → d' ≤ q →
      RealCapEstimate m d p → RealCapEstimate d d' q →
      RealCapEstimate m (KakeyaScalar.pivotSet m d')
        (max (KakeyaScalar.pivotSet m d') (KakeyaScalar.pivotDensity p q)))
    {n : ℕ} (hn : 6 ≤ n) :
    DiagonalDiscreteEstimate n (KakeyaScalar.limitProfile ((n:ℝ)-1)) :=
  conditional_diagonal_endpoint (fun _ h => FractionalSeed.fractional_real_cap_seed h) pivot hn

end KakeyaFormal.SeededEndpoint
