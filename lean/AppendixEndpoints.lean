import MainMaximal
import FractionalSeedFullRange

/-! Explicit endpoint conclusions of AppendixA in every integer dimension
n>=5. The stronger proved endpoint (or the actual fractional seed at n=5)
and valid diagonal weakening supply these conclusions; no bush iteration
or Gaussian projection construction is claimed in this module. -/
namespace KakeyaFormal.AppendixEndpoints
noncomputable section

/-- The stronger main endpoint dominates the AppendixA.2 limit for n>=6. -/
theorem bush_le_main {n : ℕ} (hn : 6 ≤ n) :
    (4*(n:ℝ)+4)/7 ≤ KakeyaScalar.limitProfile ((n:ℝ)-1) := by
  have hnR : (6:ℝ) ≤ n := by exact_mod_cast hn
  have hs : (4:ℝ)/7 ≤ KakeyaScalar.slopeLimit := by
    dsimp [KakeyaScalar.slopeLimit]
    linarith [KakeyaScalar.sqrt_two_rational_bounds.2]
  have hp := mul_nonneg (sub_nonneg.mpr hs) (sub_nonneg.mpr hnR)
  have hlo := KakeyaScalar.slopeLimit_bounds.1
  dsimp [KakeyaScalar.limitProfile]
  nlinarith

/-- The actual diagonal conclusion (A.3), including n=5. -/
theorem bush_discrete {n : ℕ} (hn : 5 ≤ n) :
    DiagonalDiscreteEstimate n ((4*(n:ℝ)+4)/7) := by
  by_cases heq : n=5
  · subst n
    have hseed : DiagonalDiscreteEstimate 5 ((7:ℝ)/2) := by
      convert FractionalSeedFullRange.fractional_discrete_seed 3 (m:=4) (by norm_num) using 1
      norm_num [DiagonalDiscreteEstimate]
    exact hseed.weaken (by norm_num)
  · have hn6 : 6 ≤ n := by omega
    exact (MainEndpoint.diagonal_discrete hn6).weaken (bush_le_main hn6)

/-- The weaker-set bush fixed point in AppendixA.3, with the density exponent
weakened by the proved actual integer-shading argument. -/
theorem weakened_bush_discrete {n : ℕ} (hn : 5 ≤ n) :
    DiagonalDiscreteEstimate n ((4*(n:ℝ)+3)/7) :=
  (bush_discrete hn).weaken (by linarith)

/-- Literal cap-free, arbitrary-position maximal-shading conclusion (A.3). -/
theorem bush_maximal {n : ℕ} (hn : 5 ≤ n) :
    MaximalShading.Estimate n ((4*(n:ℝ)+4)/7) := by
  cases n with
  | zero => omega
  | succ k =>
    have hnR : (5:ℝ) ≤ k+1 := by exact_mod_cast hn
    exact MainMaximal.from_diagonal (k:=k) (bush_discrete hn) (by push_cast; linarith)

/-- Literal cap-free, arbitrary-position maximal-shading conclusion A.3. -/
theorem weakened_bush_maximal {n : ℕ} (hn : 5 ≤ n) :
    MaximalShading.Estimate n ((4*(n:ℝ)+3)/7) := by
  cases n with
  | zero => omega
  | succ k =>
    have hnR : (5:ℝ) ≤ k+1 := by exact_mod_cast hn
    exact MainMaximal.from_diagonal (k:=k) (weakened_bush_discrete hn) (by push_cast; linarith)

end
end KakeyaFormal.AppendixEndpoints
