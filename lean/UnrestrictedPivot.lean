import TwoEndsGlobalization
import TwoEndsPivot
import SeededEndpoint
import MeasurableEstimate

/-! Assemble the actual all-angle theorem and two-ends globalization.
The real-cap pivot and its recursive endpoint have no supplied pivot,
localization, sampling, or published-axiom premise. -/
namespace KakeyaFormal.UnrestrictedPivot
noncomputable section

/-- The unrestricted pivot in every adequate integer ambient dimension.
Its analytic base and lift are the literal RealCapEstimate predicates. -/
theorem real_cap_pivot (m d d' p q : ℝ)
    (hd' : 3 < d') (hdd' : d' < d) (hdm : d < m) (hdp : d ≤ p) (hdq : d' ≤ q)
    (hbase : RealCapEstimate m d p) (hlift : RealCapEstimate d d' q) :
    RealCapEstimate m (KakeyaScalar.pivotSet m d')
      (max (KakeyaScalar.pivotSet m d') (KakeyaScalar.pivotDensity p q)) := by
  intro n hmn
  have hm : 3 < m := hd'.trans (hdd'.trans hdm)
  have hn2 : 2 ≤ n := by
    by_contra h
    have hn : n ≤ 1 := by omega
    have hnR : (n:ℝ) ≤ 1 := by exact_mod_cast hn
    linarith
  let k := n-2
  have hn : n=k+2 := by dsimp [k]; omega
  rw [hn] at hmn ⊢
  have hmn' : m+1 ≤ (k:ℝ)+2 := by push_cast at hmn; linarith
  have hdk : d ≤ ((k+3:ℕ):ℝ)-1 := by push_cast; linarith
  have hD : KakeyaScalar.pivotSet m d' < m := by
    dsimp [KakeyaScalar.pivotSet]
    linarith
  have hD1 : 1 ≤ KakeyaScalar.pivotSet m d' := by
    dsimp [KakeyaScalar.pivotSet]
    linarith
  have hC1 : 1 ≤ KakeyaScalar.pivotDensity p q := by
    dsimp [KakeyaScalar.pivotDensity]
    linarith
  have hmargin : 0 < (m+3)/2-KakeyaScalar.pivotSet m d'+
      (KakeyaScalar.pivotDensity p q-2)/3 := by
    dsimp [KakeyaScalar.pivotSet,KakeyaScalar.pivotDensity]
    linarith
  have htwo := TwoEndsPivot.from_base_and_lift (k:=k) (hbase (k+2) hmn)
    (hlift (k+3) hdk) (by linarith : 1 ≤ m) hmn'
    (by linarith : 1 ≤ p) (by linarith : 0 ≤ d) (by linarith : 2 ≤ q) hD hmargin
  exact TwoEndsGlobalization.remove_two_ends (k:=k+1) htwo
    (by linarith : 0 ≤ m) hD1 hC1

/-- Constructive real-cap endpoint: both the fractional seed and unrestricted
pivot have been proved for the actual configurations. -/
theorem real_cap_endpoint {m : ℝ} (hm : 3 < m) :
    RealCapEstimate m (KakeyaScalar.limitProfile m)
      (max (KakeyaScalar.limitProfile m) 4) :=
  SeededEndpoint.real_cap_endpoint_from_pivot real_cap_pivot hm

/-- Exact diagonal endpoint in every integer dimension n≥6. -/
theorem diagonal_endpoint {n : ℕ} (hn : 6 ≤ n) :
    DiagonalDiscreteEstimate n (KakeyaScalar.limitProfile ((n:ℝ)-1)) :=
  SeededEndpoint.diagonal_endpoint_from_pivot real_cap_pivot hn

end
end KakeyaFormal.UnrestrictedPivot
