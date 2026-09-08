import Localization

/-! A finite dyadic depth with an explicit logarithmic bound, for every real
mesh scale. The coarser bottom scale lies between δ and 2δ. -/
namespace KakeyaFormal.ScaleChoice
open KakeyaFormal.Localization

theorem dyadic_depth {δ : ℝ} (hδ : 0 < δ) (hδ1 : δ ≤ 1) :
    ∃ J : ℕ, δ ≤ radius J 0 ∧ radius J 0 < 2*δ ∧
      (J:ℝ) ≤ Real.log (1/δ)/Real.log 2 := by
  have hN : (1:ℝ) ≤ 1/δ := (le_div_iff₀ hδ).mpr (by simpa using hδ1)
  obtain ⟨J,hlo,hhi⟩ := exists_nat_pow_near hN (by norm_num : (1:ℝ) < 2)
  have hp : 0 < (2:ℝ)^J := by positivity
  have hlo' : (2:ℝ)^J*δ ≤ 1 := (le_div_iff₀ hδ).mp hlo
  have hhi' : 1 < (2:ℝ)^(J+1)*δ := (div_lt_iff₀ hδ).mp hhi
  rw [pow_succ] at hhi'
  refine ⟨J,?_,?_,?_⟩
  · unfold radius
    rw [pow_zero]
    exact (le_div_iff₀ hp).mpr (by nlinarith)
  · unfold radius
    rw [pow_zero]
    exact (div_lt_iff₀ hp).mpr (by nlinarith)
  · have hl := Real.log_le_log hp hlo
    rw [Real.log_pow] at hl
    exact (le_div_iff₀ (Real.log_pos (by norm_num))).mpr hl

/-- Every positive bounded mass interval has a dyadic class budget controlled by
its logarithmic ratio, including an extra class for the top endpoint. -/
theorem dyadic_class_budget {lower upper : ℝ}
    (hlower : 0 < lower) (hlu : lower ≤ upper) :
    ∃ J : ℕ, upper ≤ (2:ℝ)^J*lower ∧
      (J:ℝ)+1 ≤ Real.log (upper/lower)/Real.log 2+2 := by
  have hratio : (1:ℝ) ≤ upper/lower := (le_div_iff₀ hlower).mpr (by simpa using hlu)
  obtain ⟨n,hlo,hhi⟩ := exists_nat_pow_near hratio (by norm_num : (1:ℝ) < 2)
  refine ⟨n+1,((div_lt_iff₀ hlower).mp hhi).le,?_⟩
  have hp : 0 < (2:ℝ)^n := by positivity
  have hlog := Real.log_le_log hp hlo
  rw [Real.log_pow] at hlog
  have hn := (le_div_iff₀ (Real.log_pos (by norm_num : (1:ℝ) < 2))).mpr hlog
  push_cast
  linarith

end KakeyaFormal.ScaleChoice
