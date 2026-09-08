import MarkedNormalizationKappa
import Mathlib.Analysis.Complex.ExponentialBounds

/-! The sharp minimum-scale logarithmic exponent from manuscript section 5.8.
The positive prefactor depends on the fixed geometric constant, alpha, B0 and
theta0, but is independent of the logarithmic budget A and the configuration.
The source range N >= 2 guarantees log(2N) >= 1 without a floor loss. -/
namespace KakeyaFormal.MinPivotLogBudget
noncomputable section

def prefactor (c B0 alpha theta0 : ℝ) : ℝ :=
  c * min theta0 (min (1/100) ((c/B0)^(1/alpha)))

theorem prefactor_pos {c B0 alpha theta0 : ℝ}
    (hc : 0 < c) (hB0 : 0 < B0) (ht0 : 0 < theta0) :
    0 < prefactor c B0 alpha theta0 := by
  unfold prefactor
  positivity

/-- A generic minimum, with the same fixed constant inside and outside the
concentration power, has the maximum of the two logarithmic losses. -/
theorem minimum_lower {c B0 alpha theta0 B theta L A : ℝ}
    (hc : 0 < c) (hB0 : 0 < B0) (ha : 0 < alpha) (ht0 : 0 < theta0)
    (hB : 0 < B) (hL : 1 ≤ L) (hA : 0 ≤ A)
    (hBB : B ≤ B0*L^A) (htheta : theta0*L^(-A) ≤ theta) :
    prefactor c B0 alpha theta0 * L^(-(A*max 1 (1/alpha))) ≤
      c*min theta (min (1/100) ((c/B)^(1/alpha))) := by
  have hL0 : 0 < L := by linarith
  have hLp : 0 < L^A := Real.rpow_pos_of_pos hL0 A
  have hAmax : A ≤ A*max 1 (1/alpha) := by
    simpa only [mul_one] using mul_le_mul_of_nonneg_left (le_max_left 1 (1/alpha)) hA
  have hAdiv : A/alpha ≤ A*max 1 (1/alpha) := by
    simpa only [mul_one_div] using mul_le_mul_of_nonneg_left (le_max_right 1 (1/alpha)) hA
  have hpowA := Real.rpow_le_rpow_of_exponent_le hL (neg_le_neg hAmax)
  have hpowDiv := Real.rpow_le_rpow_of_exponent_le hL (neg_le_neg hAdiv)
  have hpowOne : L^(-(A*max 1 (1/alpha))) ≤ 1 := by
    simpa only [Real.rpow_zero] using Real.rpow_le_rpow_of_exponent_le hL
      (show -(A*max 1 (1/alpha)) ≤ 0 by linarith)
  have hratio : c/(B0*L^A) ≤ c/B :=
    div_le_div_of_nonneg_left hc.le hB hBB
  have hpower := Real.rpow_le_rpow (by positivity : 0 ≤ c/(B0*L^A)) hratio
    (by positivity : 0 ≤ 1/alpha)
  have heq : (c/(B0*L^A))^(1/alpha) =
      (c/B0)^(1/alpha)*L^(-(A/alpha)) := by
    rw [Real.div_rpow hc.le (mul_pos hB0 hLp).le,
      Real.mul_rpow hB0.le hLp.le, ← Real.rpow_mul hL0.le,
      Real.div_rpow hc.le hB0.le, Real.rpow_neg hL0.le]
    simp only [mul_one_div]
    ring
  rw [heq] at hpower
  let u := min theta0 (min (1/100:ℝ) ((c/B0)^(1/alpha)))
  have hu : 0 ≤ u := by dsimp [u]; positivity
  have huTheta : u ≤ theta0 := min_le_left _ _
  have huSmall : u ≤ (1/100:ℝ) := (min_le_right _ _).trans (min_le_left _ _)
  have huPower : u ≤ (c/B0)^(1/alpha) := (min_le_right _ _).trans (min_le_right _ _)
  unfold prefactor
  rw [mul_assoc]
  apply mul_le_mul_of_nonneg_left _ hc.le
  apply le_min
  · exact (mul_le_mul huTheta hpowA (by positivity) ht0.le).trans htheta
  · apply le_min
    · exact (mul_le_mul_of_nonneg_right huSmall (by positivity)).trans
        (by simpa only [mul_one] using mul_le_mul_of_nonneg_left hpowOne (by norm_num : (0:ℝ) ≤ 1/100))
    · exact (mul_le_mul huPower hpowDiv (by positivity) (by positivity)).trans hpower

theorem source_lower {width B0 alpha theta0 B theta L A : ℝ}
    (hw : 0 ≤ width) (hB0 : 0 < B0) (ha : 0 < alpha) (ht0 : 0 < theta0)
    (hB : 0 < B) (hL : 1 ≤ L) (hA : 0 ≤ A)
    (hBB : B ≤ B0*L^A) (htheta : theta0*L^(-A) ≤ theta) :
    prefactor (MinPivotKappa.sourceConstant width) B0 alpha theta0 *
      L^(-(A*max 1 (1/alpha))) ≤ MinPivotKappa.sourceChoice width B alpha theta :=
  minimum_lower (MinPivotKappa.sourceConstant_bounds hw).1 hB0 ha ht0 hB hL hA hBB htheta

/-- The same sharp bound applies after actual marked-grid/length normalization;
the normalization factor is retained inside the prefactor's concentration power. -/
theorem normalized_lower {width C B0 alpha theta0 B theta L A : ℝ}
    (hw : 0 ≤ width) (hC : 1 ≤ C) (hB0 : 0 < B0) (ha : 0 < alpha) (ht0 : 0 < theta0)
    (hB : 0 < B) (hL : 1 ≤ L) (hA : 0 ≤ A)
    (hBB : B ≤ B0*L^A) (htheta : theta0*L^(-A) ≤ theta) :
    prefactor (MarkedNormalizationKappa.sourceConstant width C) B0 alpha theta0 *
      L^(-(A*max 1 (1/alpha))) ≤ MarkedNormalizationKappa.choice width C B alpha theta :=
  minimum_lower (MarkedNormalizationKappa.sourceConstant_bounds hw hC).1 hB0 ha ht0 hB hL hA hBB htheta

theorem source_log_ge_one {N : ℝ} (hN : 2 ≤ N) : 1 ≤ Real.log (2*N) := by
  have hh : Real.exp 1 ≤ 2*N := by linarith [Real.exp_one_lt_three]
  simpa only [Real.log_exp] using Real.log_le_log (Real.exp_pos 1) hh

/-- Literal source notation, uniform in A, B, theta and N >= 2. -/
theorem source_notation {width B0 alpha theta0 : ℝ}
    (hw : 0 ≤ width) (hB0 : 0 < B0) (ha : 0 < alpha) (ht0 : 0 < theta0) :
    ∃ c0 : ℝ, 0 < c0 ∧ ∀ A B theta N : ℝ, 0 ≤ A → 0 < B → 2 ≤ N →
      B ≤ B0*(Real.log (2*N))^A →
      theta0*(Real.log (2*N))^(-A) ≤ theta →
      c0*(Real.log (2*N))^(-(A*max 1 (1/alpha))) ≤
        MinPivotKappa.sourceChoice width B alpha theta := by
  refine ⟨prefactor (MinPivotKappa.sourceConstant width) B0 alpha theta0,
    prefactor_pos (MinPivotKappa.sourceConstant_bounds hw).1 hB0 ht0, ?_⟩
  intro A B theta N hA hB hN hBB htheta
  exact source_lower hw hB0 ha ht0 hB (source_log_ge_one hN) hA hBB htheta

end
end KakeyaFormal.MinPivotLogBudget
