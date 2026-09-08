import PositiveTwoEndsSmallScaleInputs
import WideTwoEndsEstimate

/-! The source angular proposition with every p>0 and arbitrary fixed positive
full-density multiples. Analytic premises are required only for N>=2; actual
unmarked row trimming precedes the constructed angular and marked selection. -/
namespace KakeyaFormal.PositiveWideTwoEndsPivot
noncomputable section

/-- Original full shadings with any fixed comparable-density interval, all
fixed geometric normalizations, and actual full two ends. No marked broadness,
angular decomposition, sampled outcome or local analytic estimate is supplied. -/
theorem from_source_inputs {k : ℕ} {m d d' p q : ℝ}
    (hbase : SourceAnalyticInputs.Base (k+2) m d p)
    (hlift : SourceAnalyticInputs.Lifted (k+3) d d' q)
    (hm : 1 ≤ m) (hmn : m+1 ≤ (k:ℝ)+2)
    (hp : 0 < p) (hd : 0 ≤ d) (hq : 2 ≤ q)
    (hD : KakeyaScalar.pivotSet m d' < m)
    (hmargin : 0 < (m+3)/2-KakeyaScalar.pivotSet m d'+
      (KakeyaScalar.pivotDensity p q-2)/3)
    (geom : Normalization) (c₀ C₀ B alpha eps : ℝ)
    (hc₀ : 0 < c₀) (hC₀ : 0 < C₀) (hB : 1 ≤ B)
    (halpha : 0 < alpha) (heps : 0 < eps) :
    ∃ c : ℝ, 0 < c ∧ ∀ {M : ℕ} (F : TubeFamily (k+2) M) {δ lam A : ℝ},
      0 < δ → δ ≤ 1 → 0 < lam → lam ≤ 1 → 1 ≤ A →
      F.Admissible geom.width δ → F.Separated (geom.separation*δ) →
      F.Bounded geom.radius → F.CapBound δ m A →
      (∀ i, c₀*lam/δ ≤ ((F.shade i).card:ℝ)) →
      (∀ i, ((F.shade i).card:ℝ) ≤ C₀*lam/δ) →
      F.FullTwoEnds δ B alpha →
      c*A⁻¹*δ^(m-KakeyaScalar.pivotSet m d'+eps)*
        lam^(KakeyaScalar.pivotDensity p q)*(M:ℝ) ≤ (F.unionCells.card:ℝ) := by
  have htwo := PositiveTwoEndsPivot.from_source_small_scale_inputs hbase hlift hm hmn hp hd hq hD hmargin
  exact WideTwoEndsEstimate.from_two_ends htwo
    (by dsimp [KakeyaScalar.pivotDensity]; linarith) geom c₀ C₀ B alpha eps
    hc₀ hC₀ hB halpha heps

end
end KakeyaFormal.PositiveWideTwoEndsPivot
