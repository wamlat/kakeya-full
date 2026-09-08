import UnrestrictedPivot
import MaximalShading

/-! Actual measurable recursive endpoints and exact dimension6/8 limits.
The fractional seeds, unrestricted pivot, finite-stage iteration and endpoint
loss allocation are all proved. No analytic or published-result axiom is an
input. Cap-free maximal conclusions here explicitly retain fixed bounded
position normalization; the arbitrary-position conversion is separate. -/
namespace KakeyaFormal.MainEndpoint
noncomputable section

/-- The endpoint remains strictly above three for every real cap parameter
in the manuscript's range. -/
theorem limit_gt_three {m : ℝ} (hm : 3 < m) : 3 < KakeyaScalar.limitProfile m := by
  have hs : 0 < KakeyaScalar.slopeLimit := by linarith [KakeyaScalar.slopeLimit_bounds.1]
  have hp := mul_pos hs (sub_pos.mpr hm)
  dsimp [KakeyaScalar.limitProfile]
  linarith

/-- The actual real-cap measurable endpoint in every adequate integer ambient
dimension, with the full density envelope max(limitProfile(m),4). -/
theorem real_cap_measurable {m : ℝ} (hm : 3 < m) :
    RealCapMeasurableEstimate m (KakeyaScalar.limitProfile m)
      (max (KakeyaScalar.limitProfile m) 4) :=
  (UnrestrictedPivot.real_cap_endpoint hm).to_measurable
    (by linarith [limit_gt_three hm]) (le_max_left _ _)

/-- Exact diagonal finite-grid endpoint for every integer dimension at least6. -/
theorem diagonal_discrete {n : ℕ} (hn : 6 ≤ n) :
    DiagonalDiscreteEstimate n (KakeyaScalar.limitProfile ((n:ℝ)-1)) :=
  UnrestrictedPivot.diagonal_endpoint hn

/-- Arbitrary measurable shadings in every fixed geometric normalization. -/
theorem diagonal_measurable {n : ℕ} (hn : 6 ≤ n) :
    MeasurableEstimate n ((n:ℝ)-1) (KakeyaScalar.limitProfile ((n:ℝ)-1))
      (KakeyaScalar.limitProfile ((n:ℝ)-1)) := by
  have hnR : (6:ℝ) ≤ n := by exact_mod_cast hn
  exact (diagonal_discrete hn).to_measurable (by omega)
    (by linarith [KakeyaScalar.limit_diagonal_for_n_ge_six hnR]) le_rfl

/-- The manuscript's actual sum-of-tube-volumes form at the exact endpoint. -/
theorem diagonal_volume {n : ℕ} (hn : 6 ≤ n) :
    VolumeMeasurableEstimate n ((n:ℝ)-1) (KakeyaScalar.limitProfile ((n:ℝ)-1))
      (KakeyaScalar.limitProfile ((n:ℝ)-1)) :=
  (diagonal_measurable hn).volume_form

/-- The full ambient cap bound follows from the actual direction separation.
No cap coefficient or cap hypothesis remains in this bounded-position result. -/
theorem bounded_maximal {n : ℕ} (hn : 6 ≤ n) :
    MaximalShading.BoundedEstimate n (KakeyaScalar.limitProfile ((n:ℝ)-1)) := by
  cases n with
  | zero => omega
  | succ k =>
    apply MaximalShading.bounded_maximal_of_volume (k:=k)
    simpa only [Nat.cast_add,Nat.cast_one,add_sub_cancel_right] using
      (diagonal_volume (n:=k+1) hn)

/-- Exact algebraic six-dimensional finite endpoint. -/
theorem six_discrete : DiscreteEstimate 6 5 (7-2*Real.sqrt 2) (7-2*Real.sqrt 2) := by
  have h := diagonal_discrete (n:=6) (by norm_num)
  norm_num only [DiagonalDiscreteEstimate,Nat.cast_ofNat,show (6:ℝ)-1=5 by norm_num] at h
  rwa [KakeyaScalar.dimension_six_limit] at h

/-- Exact algebraic eight-dimensional finite endpoint. -/
theorem eight_discrete : DiscreteEstimate 8 7 (11-4*Real.sqrt 2) (11-4*Real.sqrt 2) := by
  have h := diagonal_discrete (n:=8) (by norm_num)
  norm_num only [DiagonalDiscreteEstimate,Nat.cast_ofNat,show (8:ℝ)-1=7 by norm_num] at h
  rwa [KakeyaScalar.dimension_eight_limit] at h

/-- Arbitrary measurable six-dimensional shadings at7−2sqrt2. -/
theorem six_measurable : MeasurableEstimate 6 5 (7-2*Real.sqrt 2) (7-2*Real.sqrt 2) := by
  have h := diagonal_measurable (n:=6) (by norm_num)
  norm_num only [Nat.cast_ofNat,show (6:ℝ)-1=5 by norm_num] at h
  rwa [KakeyaScalar.dimension_six_limit] at h

/-- Arbitrary measurable eight-dimensional shadings at11−4sqrt2. -/
theorem eight_measurable : MeasurableEstimate 8 7 (11-4*Real.sqrt 2) (11-4*Real.sqrt 2) := by
  have h := diagonal_measurable (n:=8) (by norm_num)
  norm_num only [Nat.cast_ofNat,show (8:ℝ)-1=7 by norm_num] at h
  rwa [KakeyaScalar.dimension_eight_limit] at h

/-- The cap-free six-dimensional endpoint, within each fixed bounded region. -/
theorem six_bounded_maximal : MaximalShading.BoundedEstimate 6 (7-2*Real.sqrt 2) := by
  have h := bounded_maximal (n:=6) (by norm_num)
  norm_num only [Nat.cast_ofNat,show (6:ℝ)-1=5 by norm_num] at h
  rwa [KakeyaScalar.dimension_six_limit] at h

/-- The cap-free eight-dimensional endpoint, within each fixed bounded region. -/
theorem eight_bounded_maximal : MaximalShading.BoundedEstimate 8 (11-4*Real.sqrt 2) := by
  have h := bounded_maximal (n:=8) (by norm_num)
  norm_num only [Nat.cast_ofNat,show (8:ℝ)-1=7 by norm_num] at h
  rwa [KakeyaScalar.dimension_eight_limit] at h

end
end KakeyaFormal.MainEndpoint
