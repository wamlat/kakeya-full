import SixDimensionalCore
import AllAnglePivot

/-! The actual six-dimensional ALL-ANGLE bound under original full two ends.
The base and seven-dimensional lifted estimates are proved fractional seeds.
No marked, broadness, decomposition, sampling or logarithmic-budget input
remains. This is a two-ends theorem, not the unrestricted M6(33/8) assertion. -/
namespace KakeyaFormal.SixDimensionalAllAngles
open Finset
noncomputable section

/-- Exact D=33/8, density exponent C=15/4, and sparse margin 11/24.
The positive constant precedes every actual family, scale, density, cap
coefficient and population. The union is the literal original finite union. -/
theorem two_ends_estimate (width R B alpha eps : ℝ)
    (hB : 1 ≤ B) (halpha : 0 < alpha) (heps : 0 < eps) :
    ∃ c : ℝ, 0 < c ∧ ∀ {M : ℕ} (F : TubeFamily 6 M) {δ lam A : ℝ},
      0 < δ → δ ≤ 1 → 0 < lam → lam ≤ 1 → 1 ≤ A →
      F.Admissible width δ → F.Separated δ → F.Bounded R → F.CapBound δ 5 A →
      F.Comparable δ lam →
      (∀ i x r, δ ≤ r → r ≤ 1 →
        (((F.shade i).filter (fun z => dist (cellCenter δ z) x ≤ r)).card:ℝ) ≤
          B*r^alpha*((F.shade i).card:ℝ)) →
      c*A⁻¹*δ^((7:ℝ)/8+eps)*lam^((15:ℝ)/4)*(M:ℝ) ≤ (F.unionCells.card:ℝ) := by
  have hmargin : (5+3:ℝ)/2-KakeyaScalar.pivotSet 5 (7/2)+
      (KakeyaScalar.pivotDensity 4 (7/2)-2)/3 = (11:ℝ)/24 := by
    norm_num [KakeyaScalar.pivotSet,KakeyaScalar.pivotDensity]
  have h := AllAnglePivot.all_scales (k:=4) SixDimensionalCore.base SixDimensionalCore.lift
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [KakeyaScalar.pivotSet]) width R B alpha eps hB halpha heps
    (by rw [hmargin]; norm_num)
  norm_num [KakeyaScalar.pivotSet,KakeyaScalar.pivotDensity] at h
  exact h

end
end KakeyaFormal.SixDimensionalAllAngles
