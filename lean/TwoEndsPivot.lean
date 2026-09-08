import TwoEndsDiscreteEstimate
import AllAngleSeparation
import SixDimensionalCore

/-! The actual all-angle pivot supplies the concrete two-ends interface for
EVERY fixed geometric normalization, including arbitrary positive direction
separation. The six-dimensional inputs are proved seeds, not custom axioms. -/
namespace KakeyaFormal.TwoEndsPivot
noncomputable section

/-- The only analytic assumptions are the actual base and lifted estimates.
All full two-ends and geometric hypotheses occur literally in the concrete
interface; no marked or angular premise is added. -/
theorem from_base_and_lift {k : ℕ} {m d d' pExp qExp : ℝ}
    (hbase : DiscreteEstimate (k+2) m d pExp)
    (hlift : DiscreteEstimate (k+3) d d' qExp)
    (hm : 1 ≤ m) (hmn : m+1 ≤ (k:ℝ)+2)
    (hp : 1 ≤ pExp) (hd : 0 ≤ d) (hq : 2 ≤ qExp)
    (hD : KakeyaScalar.pivotSet m d' < m)
    (hmargin : 0 < (m+3)/2-KakeyaScalar.pivotSet m d'+
      (KakeyaScalar.pivotDensity pExp qExp-2)/3) :
    TwoEndsDiscreteEstimate (k+2) m (KakeyaScalar.pivotSet m d')
      (KakeyaScalar.pivotDensity pExp qExp) := by
  intro geom B alpha eps hB halpha heps
  exact AllAngleSeparation.configuration_estimate hbase hlift hm hmn hp hd hq hD
    geom B alpha eps hB halpha heps hmargin

/-- The standard-only six-dimensional all-angle estimate, now in every fixed
ShadedConfiguration normalization. Original full two ends remains explicit. -/
theorem six_dimensional : TwoEndsDiscreteEstimate 6 5 (33/8) (15/4) := by
  have h := from_base_and_lift (k:=4) SixDimensionalCore.base SixDimensionalCore.lift
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [KakeyaScalar.pivotSet])
    (by norm_num [KakeyaScalar.pivotSet,KakeyaScalar.pivotDensity])
  norm_num [KakeyaScalar.pivotSet,KakeyaScalar.pivotDensity] at h
  exact h

/-- The diagonal density exponent is a weakening at density at most one.
This is STILL a full-two-ends estimate, not unrestricted M6(33/8). -/
theorem six_dimensional_diagonal : TwoEndsDiscreteEstimate 6 5 (33/8) (33/8) :=
  six_dimensional.weaken_density (by norm_num)

end
end KakeyaFormal.TwoEndsPivot
