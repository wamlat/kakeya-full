import PositiveTwoEndsPivot
import SourceAnalyticInputs

/-! Proposition7.1 with every positive base-density exponent and analytic
premises required only for the source eccentricity N>=2. -/
namespace KakeyaFormal.PositiveTwoEndsPivot
noncomputable section

/-- Actual all-angle full-two-ends conclusion from the literal small-scale
absolute-cap base and paired-error cumulative lift. The original full shadings
are supplied; all angular, marked, sampling and four-case data are constructed. -/
theorem from_source_small_scale_inputs {k : ℕ} {m d d' pExp qExp : ℝ}
    (hbase : SourceAnalyticInputs.Base (k+2) m d pExp)
    (hlift : SourceAnalyticInputs.Lifted (k+3) d d' qExp)
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
