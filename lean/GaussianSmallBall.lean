import GaussianMatrix

/-! Concrete small-ball bounds for standard finite-dimensional Gaussians.
The exponent is the ACTUAL target dimension, obtained from independent real
coordinates and their bounded density. -/
namespace KakeyaFormal.GaussianSmallBall
open MeasureTheory ProbabilityTheory Set
open scoped ENNReal NNReal BigOperators RealInnerProductSpace
noncomputable section

/-- A simple explicit density ceiling, sufficient for polynomial small balls. -/
theorem real_density_le_one (x : ℝ) : gaussianPDF 0 1 x ≤ 1 := by
  have hpi : (1:ℝ) ≤ Real.sqrt (2*Real.pi) := Real.le_sqrt_of_sq_le (by nlinarith [Real.pi_gt_three])
  have hexp : Real.exp (-x^2/2) ≤ 1 := Real.exp_le_one_iff.mpr (by nlinarith [sq_nonneg x])
  have hs : 0 ≤ (Real.sqrt (2*Real.pi))⁻¹ := by positivity
  have hsi : (Real.sqrt (2*Real.pi))⁻¹ ≤ 1 := inv_le_one_of_one_le₀ hpi
  have hh : gaussianPDFReal 0 1 x ≤ 1 := by
    norm_num only [gaussianPDFReal,NNReal.coe_one,mul_one,sub_zero]
    nlinarith [Real.exp_pos (-x^2/2)]
  exact (ENNReal.ofReal_le_ofReal hh).trans_eq ENNReal.ofReal_one

/-- The Gaussian probability of any real set is bounded by its Lebesgue
outer measure. No measurability premise is needed for this density inequality. -/
theorem real_measure_le_volume (S : Set ℝ) : gaussianReal 0 1 S ≤ volume S := by
  rw [gaussianReal_apply 0 (by norm_num : (1:ℝ≥0) ≠ 0)]
  calc
    _ ≤ ∫⁻ _x in S, (1:ℝ≥0∞) := lintegral_mono fun x => real_density_le_one x
    _ = _ := by simp

/-- An actual standard Gaussian vector has a dimension-power small-ball bound. -/
theorem closedBall_bound (n : ℕ) {r : ℝ} (hr : 0 ≤ r) :
    stdGaussian (Space n) (Metric.closedBall 0 r) ≤ ENNReal.ofReal ((2*r)^n) := by
  rw [← map_pi_eq_stdGaussian,Measure.map_apply (by fun_prop) Metric.isClosed_closedBall.measurableSet]
  have hsub : (WithLp.toLp 2) ⁻¹' (Metric.closedBall (0:Space n) r) ⊆
      Set.univ.pi (fun _ : Fin n => Set.Icc (-r) r) := by
    intro x hx
    have hnorm : ‖(WithLp.toLp 2 x : Space n)‖ ≤ r := by simpa only [Set.mem_preimage,Metric.mem_closedBall,dist_zero_right] using hx
    intro i _
    have hc : |x i| ≤ r := by
      have hh := PiLp.norm_apply_le (WithLp.toLp 2 x : Space n) i
      have hh' : |x i| ≤ ‖(WithLp.toLp 2 x : Space n)‖ := by simpa only [Real.norm_eq_abs] using hh
      exact hh'.trans hnorm
    exact abs_le.mp hc
  calc
    _ ≤ (Measure.pi (fun _ : Fin n => gaussianReal 0 1)) (Set.univ.pi (fun _ => Set.Icc (-r) r)) := measure_mono hsub
    _ = ∏ _i : Fin n, gaussianReal 0 1 (Set.Icc (-r) r) := Measure.pi_pi _ _
    _ ≤ ∏ _i : Fin n, ENNReal.ofReal (2*r) := by
      apply Finset.prod_le_prod'
      intro i _
      exact (real_measure_le_volume _).trans_eq (by rw [Real.volume_Icc]; congr 1; ring)
    _ = _ := by
      simpa only [Finset.prod_const,Finset.card_univ,Fintype.card_fin] using
        (ENNReal.ofReal_pow (by positivity : 0 ≤ 2*r) n).symm

/-- Probability saturation is included explicitly; at dimension four this is
min(1,16*r^4), not a five-dimensional collision exponent. -/
theorem closedBall_min_bound (n : ℕ) {r : ℝ} (hr : 0 ≤ r) :
    stdGaussian (Space n) (Metric.closedBall 0 r) ≤ min 1 (ENNReal.ofReal ((2*r)^n)) :=
  le_min (prob_le_one) (closedBall_bound n hr)

end
end KakeyaFormal.GaussianSmallBall
