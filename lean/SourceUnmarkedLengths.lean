import UnmarkedLengthEstimates
import PositiveTwoEndsSmallScaleInputs

/-! Named source Propositions 7.1 and 8.1 on actual original bounded-length
axes. The analytic inputs use only the source eccentricity cutoff N>=2;
the original integer union and all fixed geometric constants are explicit. -/
namespace KakeyaFormal.SourceUnmarkedLengths
noncomputable section

/-- Full positive-p angular proposition with all fixed original axis lengths,
row-density multiples and direction-separation normalizations. -/
theorem angular {k : ℕ} {m d d' p q : ℝ}
    (hbase : SourceAnalyticInputs.Base (k+2) m d p)
    (hlift : SourceAnalyticInputs.Lifted (k+3) d d' q)
    (hm : 1 ≤ m) (hmn : m+1 ≤ (k:ℝ)+2)
    (hp : 0 < p) (hd : 0 ≤ d) (hq : 2 ≤ q)
    (hD : KakeyaScalar.pivotSet m d' < m)
    (hmargin : 0 < (m+3)/2-KakeyaScalar.pivotSet m d'+
      (KakeyaScalar.pivotDensity p q-2)/3)
    (geom : Normalization) (lengthUpper c₀ C₀ B alpha eps : ℝ)
    (hc₀ : 0 < c₀) (hC₀ : 0 < C₀) (hB : 1 ≤ B)
    (halpha : 0 < alpha) (heps : 0 < eps) :
    ∃ c : ℝ, 0 < c ∧ ∀ {M : ℕ} (F : TubeFamily (k+2) M) (lengths : Fin M → ℝ)
      {δ lam A : ℝ},
      0 < δ → δ ≤ 1 → 0 < lam → lam ≤ 1 → 1 ≤ A →
      (∀ i, lengths i ≤ lengthUpper) →
      (∀ i z, z ∈ F.shade i → cellCenter δ z ∈
        SamplingGeometry.lengthCarrier (F.tube i) (lengths i) (geom.width*δ)) →
      F.Separated (geom.separation*δ) → F.Bounded geom.radius → F.CapBound δ m A →
      (∀ i, c₀*lam/δ ≤ ((F.shade i).card:ℝ)) →
      (∀ i, ((F.shade i).card:ℝ) ≤ C₀*lam/δ) →
      F.FullTwoEnds δ B alpha →
      c*A⁻¹*δ^(m-KakeyaScalar.pivotSet m d'+eps)*
        lam^(KakeyaScalar.pivotDensity p q)*(M:ℝ) ≤ (F.unionCells.card:ℝ) := by
  have htwo := PositiveTwoEndsPivot.from_source_small_scale_inputs
    hbase hlift hm hmn hp hd hq hD hmargin
  exact UnmarkedLengthEstimates.from_two_ends htwo (by linarith)
    (by dsimp [KakeyaScalar.pivotDensity]; linarith)
    geom lengthUpper c₀ C₀ B alpha eps hc₀ hC₀ hB halpha heps

/-- The unrestricted proposition from only the absolute-cap N>=2 two-ends
premise, on actual original bounded-length axes. No upper row-density bound,
lambda<=1, angular condition or original full-two-ends assumption is needed. -/
theorem globalize {k : ℕ} {m D C : ℝ}
    (hestimate : SourceAnalyticInputs.TwoEnds (k+1) m D C)
    (hm : 0 ≤ m) (hD : 1 ≤ D)
    (geom : Normalization) (lengthUpper c₀ eps : ℝ) (hc₀ : 0 < c₀) (heps : 0 < eps) :
    ∃ c : ℝ, 0 < c ∧ ∀ {M : ℕ} (F : TubeFamily (k+1) M) (lengths : Fin M → ℝ)
      {δ lam A : ℝ},
      0 < δ → δ ≤ 1 → 0 < lam → 1 ≤ A →
      (∀ i, lengths i ≤ lengthUpper) →
      (∀ i z, z ∈ F.shade i → cellCenter δ z ∈
        SamplingGeometry.lengthCarrier (F.tube i) (lengths i) (geom.width*δ)) →
      F.Separated (geom.separation*δ) → F.Bounded geom.radius → F.CapBound δ m A →
      (∀ i, c₀*lam/δ ≤ ((F.shade i).card:ℝ)) →
      c*A⁻¹*δ^(m-D+eps)*lam^(max D C)*(M:ℝ) ≤ (F.unionCells.card:ℝ) :=
  UnmarkedLengthEstimates.from_discrete (hestimate.globalize hm hD) hm
    (zero_lt_one.trans_le (hD.trans (le_max_left _ _))) geom lengthUpper c₀ eps hc₀ heps

end
end KakeyaFormal.SourceUnmarkedLengths
