import Mathlib

/-! Uniform quantitative logarithmic absorption, without an unspecified limiting
argument. The constants are chosen solely from the fixed logarithmic exponent
and the requested scale loss, before the scale N varies. -/

namespace KakeyaFormal

theorem log_power_uniform_bound {P eps : ℝ} (hP : 0 ≤ P) (heps : 0 < eps) :
    ∃ C : ℝ, 0 < C ∧ ∀ N : ℝ, 1 ≤ N → (Real.log (2*N)) ^ P ≤ C * N ^ eps := by
  by_cases hzero : P = 0
  · subst P
    refine ⟨1,by norm_num,fun N hN => ?_⟩
    simpa using Real.one_le_rpow hN heps.le
  have hPpos : 0 < P := lt_of_le_of_ne hP (Ne.symm hzero)
  let r : ℝ := eps/P
  have hr : 0 < r := div_pos heps hPpos
  refine ⟨(2 : ℝ)^eps / r^P, div_pos (Real.rpow_pos_of_pos (by norm_num) _) (Real.rpow_pos_of_pos hr _), ?_⟩
  intro N hN
  have hN0 : 0 < N := by linarith
  have h2N : 0 < 2*N := by positivity
  have hlog : 0 ≤ Real.log (2*N) := Real.log_nonneg (by linarith)
  have h := Real.rpow_le_rpow hlog (Real.log_le_rpow_div h2N.le hr) hP
  calc
    (Real.log (2*N)) ^ P ≤ ((2*N)^r/r)^P := h
    _ = (2*N)^eps/r^P := by
      rw [Real.div_rpow (Real.rpow_nonneg h2N.le _) hr.le, ← Real.rpow_mul h2N.le]
      have hid : r*P=eps := by dsimp [r]; field_simp
      rw [hid]
    _ = (2 : ℝ)^eps/r^P * N^eps := by
      rw [Real.mul_rpow (by norm_num : (0:ℝ) ≤ 2) hN0.le]
      ring

theorem inverse_log_power_uniform_bound {P eps : ℝ} (hP : 0 ≤ P) (heps : 0 < eps) :
    ∃ c : ℝ, 0 < c ∧ ∀ N : ℝ, 1 ≤ N →
      c * N ^ (-eps) ≤ (Real.log (2*N)) ^ (-P) := by
  obtain ⟨C,hC,hbound⟩ := log_power_uniform_bound hP heps
  refine ⟨C⁻¹, inv_pos.mpr hC, ?_⟩
  intro N hN
  have hN0 : 0 < N := by linarith
  have hlog : 0 < Real.log (2*N) := Real.log_pos (by linarith)
  have hinv := (one_div_le_one_div_of_le
    (Real.rpow_pos_of_pos hlog P) (hbound N hN))
  rw [Real.rpow_neg hN0.le, Real.rpow_neg hlog.le]
  simpa only [one_div, mul_inv_rev, mul_comm] using hinv

end KakeyaFormal
