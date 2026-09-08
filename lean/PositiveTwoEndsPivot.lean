import TwoEndsDiscreteEstimate
import PositiveAllAngleSeparation
import AbsoluteCapEstimates
import LiftedCumulativeInput

/-! Positive-base-density extension (p>0), reusing the constructed geometry.
 The actual all-angle pivot supplies the concrete two-ends interface for
EVERY fixed geometric normalization, including arbitrary positive direction
separation. The six-dimensional inputs are proved seeds, not custom axioms. -/
namespace KakeyaFormal.PositiveTwoEndsPivot
noncomputable section

/-- The only analytic assumptions are the actual base and lifted estimates.
All full two-ends and geometric hypotheses occur literally in the concrete
interface; no marked or angular premise is added. -/
theorem from_base_and_lift {k : ℕ} {m d d' pExp qExp : ℝ}
    (hbase : DiscreteEstimate (k+2) m d pExp)
    (hlift : DiscreteEstimate (k+3) d d' qExp)
    (hm : 1 ≤ m) (hmn : m+1 ≤ (k:ℝ)+2)
    (hp : 0 < pExp) (hd : 0 ≤ d) (hq : 2 ≤ qExp)
    (hD : KakeyaScalar.pivotSet m d' < m)
    (hmargin : 0 < (m+3)/2-KakeyaScalar.pivotSet m d'+
      (KakeyaScalar.pivotDensity pExp qExp-2)/3) :
    TwoEndsDiscreteEstimate (k+2) m (KakeyaScalar.pivotSet m d')
      (KakeyaScalar.pivotDensity pExp qExp) := by
  intro geom B alpha eps hB halpha heps
  exact PositiveAllAngleSeparation.configuration_estimate hbase hlift hm hmn hp hd hq hD
    geom B alpha eps hB halpha heps hmargin

/-- The full source p>0 angular proposition from absolute-cap base and the
literal paired-error cumulative lifted input. Original full two ends remains
explicit; no angular, marked, sample-outcome or piece estimate is supplied. -/
theorem from_source_inputs {k : ℕ} {m d d' pExp qExp : ℝ}
    (hbase : AbsoluteDiscreteEstimate (k+2) m d pExp)
    (hlift : LiftedCumulativeInput (k+3) d d' qExp)
    (hm : 1 ≤ m) (hmn : m+1 ≤ (k:ℝ)+2)
    (hp : 0 < pExp) (hd : 0 ≤ d) (hq : 2 ≤ qExp)
    (hD : KakeyaScalar.pivotSet m d' < m)
    (hmargin : 0 < (m+3)/2-KakeyaScalar.pivotSet m d'+
      (KakeyaScalar.pivotDensity pExp qExp-2)/3) :
    TwoEndsDiscreteEstimate (k+2) m (KakeyaScalar.pivotSet m d')
      (KakeyaScalar.pivotDensity pExp qExp) :=
  from_base_and_lift (hbase.to_discrete (zero_le_one.trans hm)) hlift.to_discrete
    hm hmn hp hd hq hD hmargin

end
end KakeyaFormal.PositiveTwoEndsPivot
