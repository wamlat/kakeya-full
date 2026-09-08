import MeasurableSeedEstimate

/-! Fixed coefficients for logarithmic density normalization at every scale
0<delta<=1, including log(2/delta)<1. No lower bound by one is presumed. -/
namespace KakeyaFormal.DensityLogNormalization
noncomputable section

def lowerFactor (c₀ ell : ℝ) : ℝ := min (min c₀ 1) ((Real.log 2)^ell)

def twoEndsFactor (D t : ℝ) : ℝ := max 1 D+(Real.log 2)^(-t)

theorem lowerFactor_pos {c₀ ell : ℝ} (hc : 0 < c₀) : 0 < lowerFactor c₀ ell := by
  have hlog : 0 < Real.log (2:ℝ) := Real.log_pos (by norm_num)
  unfold lowerFactor
  positivity

theorem lowerFactor_le {c₀ ell : ℝ} : lowerFactor c₀ ell ≤ c₀ ∧
    lowerFactor c₀ ell ≤ 1 ∧ lowerFactor c₀ ell ≤ (Real.log 2)^ell := by
  exact ⟨(min_le_left _ _).trans (min_le_left _ _),
    (min_le_left _ _).trans (min_le_right _ _),min_le_right _ _⟩

theorem normalized_density {c₀ ell L sigma : ℝ} (hc : 0 < c₀) (he : 0 ≤ ell)
    (hL : Real.log 2 ≤ L) (hs : 0 < sigma) (hs1 : sigma ≤ 1) :
    0 < lowerFactor c₀ ell*L^(-ell)*sigma ∧
      lowerFactor c₀ ell*L^(-ell)*sigma ≤ 1 := by
  have hlog : 0 < Real.log (2:ℝ) := Real.log_pos (by norm_num)
  have hLp := hlog.trans_le hL
  have hcpos := lowerFactor_pos (ell:=ell) hc
  have hp : lowerFactor c₀ ell ≤ L^ell := lowerFactor_le.2.2.trans
    (Real.rpow_le_rpow hlog.le hL he)
  have hf : lowerFactor c₀ ell*L^(-ell) ≤ 1 := by
    have hh := mul_le_mul_of_nonneg_right hp (Real.rpow_pos_of_pos hLp (-ell)).le
    rw [← Real.rpow_add hLp,add_neg_cancel,Real.rpow_zero] at hh
    exact hh
  refine ⟨by positivity,?_⟩
  exact (mul_le_mul_of_nonneg_right hf hs.le).trans (by simpa using hs1)

theorem twoEndsFactor_ge_one (D t : ℝ) : 1 ≤ twoEndsFactor D t := by
  have hp : 0 ≤ (Real.log 2)^(-t) := Real.rpow_nonneg (Real.log_nonneg (by norm_num)) _
  unfold twoEndsFactor
  linarith [le_max_left (1:ℝ) D]

theorem twoEndsFactor_ge (D t : ℝ) : D ≤ twoEndsFactor D t := by
  have hp : 0 ≤ (Real.log 2)^(-t) := Real.rpow_nonneg (Real.log_nonneg (by norm_num)) _
  unfold twoEndsFactor
  linarith [le_max_right (1:ℝ) D]

/-- This fixed enlargement handles both the variable two-ends coefficient and
its floor by one, even when the physical logarithm is smaller than one. -/
theorem max_one_budget (D : ℝ) {t L : ℝ} (ht : 0 ≤ t) (hL : Real.log 2 ≤ L) :
    max 1 (D*L^t) ≤ twoEndsFactor D t*L^t := by
  have hlog : 0 < Real.log (2:ℝ) := Real.log_pos (by norm_num)
  have hLp := hlog.trans_le hL
  apply max_le
  · have hh := mul_le_mul_of_nonneg_left (Real.rpow_le_rpow hlog.le hL ht)
      (Real.rpow_pos_of_pos hlog (-t)).le
    rw [← Real.rpow_add hlog,neg_add_cancel,Real.rpow_zero] at hh
    exact hh.trans (mul_le_mul_of_nonneg_right
      (by unfold twoEndsFactor; linarith [le_max_left (1:ℝ) D] :
        (Real.log 2)^(-t) ≤ twoEndsFactor D t) (Real.rpow_pos_of_pos hLp t).le)
  · exact mul_le_mul_of_nonneg_right (twoEndsFactor_ge D t) (Real.rpow_pos_of_pos hLp t).le

/-- Exact density-loss accounting, including both powers of the lower density. -/
theorem density_loss_identity {L : ℝ} (hL : 0 < L) (c sigma P ell : ℝ) :
    L^(-P)*(c*L^(-ell)*sigma)^2 = c^2*L^(-(P+2*ell))*sigma^2 := by
  have hs : (L^(-ell))^2 = L^(-2*ell) := by
    rw [← Real.rpow_natCast,← Real.rpow_mul hL.le]
    congr 1
    norm_num
    ring
  rw [mul_pow,mul_pow,hs]
  have hp : L^(-P)*L^(-2*ell) = L^(-(P+2*ell)) := by
    rw [← Real.rpow_add hL]
    congr 1
    ring
  calc
    _ = c^2*(L^(-P)*L^(-2*ell))*sigma^2 := by ring
    _ = _ := by rw [hp]

/-- The original full two-ends coefficient times the exact density ratio. -/
theorem density_ratio_identity {L c sigma delta : ℝ} (hL : 0 < L) (hc : 0 < c)
    (hs : 0 < sigma) (hd : 0 < delta) (n : ℕ) (B₀ C₀ b u ell : ℝ) :
    (B₀*L^b)*(C₀*L^u*sigma*delta^n)/(c*L^(-ell)*sigma*delta^n) =
      (B₀*C₀/c)*L^(b+u+ell) := by
  have hp : L^b*L^u/L^(-ell) = L^(b+u+ell) := by
    rw [← Real.rpow_add hL,← Real.rpow_sub hL]
    congr 1
    ring
  calc
    _ = (B₀*C₀/c)*(L^b*L^u/L^(-ell)) := by
      field_simp
    _ = _ := by rw [hp]

end
end KakeyaFormal.DensityLogNormalization
