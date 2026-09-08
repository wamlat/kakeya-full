import ActualLabelSelection
import Mathlib.Analysis.SpecialFunctions.Log.Base

/-! Explicit dimension/width constants for the actual pivot frequency and
fiber budgets. The only scale dependence is displayed as powers or logarithms. -/
namespace KakeyaFormal.PivotSelectionBudgets
open ActualLabelSelection LegalSampleSelection LegalOutputDirections ProjectiveGeometry
noncomputable section

/-- Ceiling-safe coefficient for the actual second-direction label budget. -/
def labelConstant (k : ℕ) (width : ℝ) : ℝ :=
  packingConstant k*(4*roundingConstant (k+1) width*(1+2*width))^k+1

/-- Ceiling-safe coefficient for actual original endpoint-label fibers. -/
def fiberCoefficient (k : ℕ) (width : ℝ) : ℝ :=
  PivotOutputCount.fiberConstant k (2*width)*(1+2*width)^2+1

def fiberLogCoefficient (k : ℕ) (width : ℝ) : ℝ :=
  Real.logb 2 (fiberCoefficient k width)+1

def pivotLog (s : ℝ) : ℝ := Real.logb 2 (2/s)+2

theorem labelConstant_ge_one (k : ℕ) {width : ℝ} (hw : 0 ≤ width) :
    1 ≤ labelConstant k width := by
  have hP := packingConstant_ge_one k
  have hR := roundingConstant_ge_one (k+1) hw
  unfold labelConstant
  have : 0 ≤ packingConstant k*(4*roundingConstant (k+1) width*(1+2*width))^k := by positivity
  linarith

theorem fiberCoefficient_ge_one (k : ℕ) (width : ℝ) :
    1 ≤ fiberCoefficient k width := by
  unfold fiberCoefficient PivotOutputCount.fiberConstant
  have : 0 ≤ 3*(2*(k:ℝ)+4)*(PivotOutputCount.boxConstant k (2*width))^2*(1+2*width)^2 := by positivity
  linarith

theorem fiberLogCoefficient_ge_one (k : ℕ) (width : ℝ) :
    1 ≤ fiberLogCoefficient k width := by
  have hh := Real.logb_nonneg (by norm_num : (1:ℝ) < 2)
    (fiberCoefficient_ge_one k width)
  unfold fiberLogCoefficient
  linarith

theorem pivotLog_ge_one {s : ℝ} (hs : 0 < s) (hs1 : s ≤ 1) :
    1 ≤ pivotLog s := by
  have hh := Real.logb_nonneg (by norm_num : (1:ℝ) < 2)
    ((le_div_iff₀ hs).mpr (by linarith) : (1:ℝ) ≤ 2/s)
  unfold pivotLog
  linarith

/-- Rounding upward costs one fixed additive coefficient, not a new κ power. -/
theorem labelBudget_upper (k : ℕ) {width kappa : ℝ}
    (hw : 0 ≤ width) (hk : 0 < kappa) (hk1 : kappa ≤ 1) :
    (labelBudget k width kappa : ℝ) ≤ labelConstant k width/kappa^(2*k) := by
  have hP := packingConstant_ge_one k
  have hR := roundingConstant_ge_one (k+1) hw
  have hp : 0 < kappa^(2*k) := pow_pos hk _
  have hp1 : kappa^(2*k) ≤ 1 := pow_le_one₀ hk.le hk1
  have hx : 0 ≤ packingConstant k*(4*roundingConstant (k+1) width*(1+2*width)/kappa^2)^k := by positivity
  have hc := (Nat.ceil_lt_add_one hx).le
  have hid : packingConstant k*(4*roundingConstant (k+1) width*(1+2*width)/kappa^2)^k =
      packingConstant k*(4*roundingConstant (k+1) width*(1+2*width))^k/kappa^(2*k) := by
    rw [div_pow,pow_mul]
    ring
  rw [hid] at hc
  unfold labelBudget
  rw [hid]
  refine hc.trans ?_
  unfold labelConstant
  apply (le_div_iff₀ hp).mpr
  calc
    (packingConstant k*(4*roundingConstant (k+1) width*(1+2*width))^k/kappa^(2*k)+1)*kappa^(2*k) =
        packingConstant k*(4*roundingConstant (k+1) width*(1+2*width))^k+kappa^(2*k) := by field_simp
    _ ≤ _ := by linarith

theorem fiberBudget_upper (k : ℕ) {width kappa δ : ℝ}
    (hk : 0 < kappa) (hk1 : kappa ≤ 1) (hδ : 0 < δ) (hδ1 : δ ≤ 1) :
    (fiberBudget k width kappa δ : ℝ) ≤ fiberCoefficient k width/(kappa*δ) := by
  have hd : 0 < kappa*δ := mul_pos hk hδ
  have hd1 : kappa*δ ≤ 1 := by nlinarith [mul_le_mul_of_nonneg_right hk1 hδ.le]
  have hx : 0 ≤ PivotOutputCount.fiberConstant k (2*width)*(1+2*width)^2/(kappa*δ) := by
    unfold PivotOutputCount.fiberConstant
    positivity
  have hc := (Nat.ceil_lt_add_one hx).le
  unfold fiberBudget
  refine hc.trans ?_
  unfold fiberCoefficient
  apply (le_div_iff₀ hd).mpr
  calc
    (PivotOutputCount.fiberConstant k (2*width)*(1+2*width)^2/(kappa*δ)+1)*(kappa*δ) =
        PivotOutputCount.fiberConstant k (2*width)*(1+2*width)^2+kappa*δ := by field_simp
    _ ≤ _ := by linarith

theorem fiberBudget_pos (k : ℕ) {width kappa δ : ℝ}
    (hw : 0 ≤ width) (hk : 0 < kappa) (hδ : 0 < δ) :
    0 < fiberBudget k width kappa δ := by
  have hbox := PivotOutputCount.boxConstant_pos k (2*width)
  unfold fiberBudget
  apply Nat.ceil_pos.mpr
  unfold PivotOutputCount.fiberConstant
  positivity

/-- The number of actual dyadic fiber bins is logarithmic in 1/(κδ). -/
theorem fiber_log_upper (k : ℕ) {width kappa δ : ℝ}
    (hw : 0 ≤ width) (hk : 0 < kappa) (hk1 : kappa ≤ 1)
    (hδ : 0 < δ) (hδ1 : δ ≤ 1) :
    ((Nat.log 2 (fiberBudget k width kappa δ)+1 : ℕ) : ℝ) ≤
      fiberLogCoefficient k width*pivotLog (kappa*δ) := by
  have hC : 0 < fiberCoefficient k width := zero_lt_one.trans_le (fiberCoefficient_ge_one k width)
  have hB : (0:ℝ) < fiberBudget k width kappa δ := by exact_mod_cast fiberBudget_pos k hw hk hδ
  have hd : 0 < kappa*δ := mul_pos hk hδ
  have hL := pivotLog_ge_one hd (by nlinarith [mul_le_mul_of_nonneg_right hk1 hδ.le])
  have hlogC := Real.logb_nonneg (by norm_num : (1:ℝ) < 2) (fiberCoefficient_ge_one k width)
  have hb := Real.natLog_le_logb (fiberBudget k width kappa δ) 2
  have hc := Real.logb_le_logb_of_le (by norm_num : (1:ℝ) < 2) hB
    (fiberBudget_upper k hk hk1 hδ hδ1)
  have hid : Real.logb 2 (fiberCoefficient k width/(kappa*δ)) =
      Real.logb 2 (fiberCoefficient k width)+pivotLog (kappa*δ)-3 := by
    unfold pivotLog
    rw [Real.logb_div hC.ne' hd.ne',Real.logb_div (by norm_num : (2:ℝ) ≠ 0) hd.ne']
    norm_num
    ring
  norm_num only [Nat.cast_add,Nat.cast_one,Nat.cast_ofNat] at hb ⊢
  rw [hid] at hc
  unfold fiberLogCoefficient
  nlinarith

/-- The collision-shell logarithm is controlled by the same fiber logarithm. -/
theorem pivotLog_mul_lower {kappa δ : ℝ}
    (hk : 0 < kappa) (hk1 : kappa ≤ 1) (hδ : 0 < δ) :
    pivotLog δ ≤ pivotLog (kappa*δ) := by
  have hh := Real.logb_le_logb_of_le (by norm_num : (1:ℝ) < 2)
    (by positivity : 0 < 2/δ)
    (div_le_div_of_nonneg_left (by norm_num : (0:ℝ) ≤ 2) (mul_pos hk hδ)
      (by nlinarith : kappa*δ ≤ δ))
  unfold pivotLog
  linarith

/-- A polynomial lower bound on κ reduces both logarithms to the usual δ log. -/
theorem pivotLog_mul_upper {kappa δ : ℝ} (q : ℕ)
    (hk : 0 < kappa) (hδ : 0 < δ) (hpoly : δ^q ≤ kappa) :
    pivotLog (kappa*δ) ≤ (q+1 : ℝ)*pivotLog δ := by
  have hh := Real.logb_le_logb_of_le (by norm_num : (1:ℝ) < 2) (pow_pos hδ q) hpoly
  rw [Real.logb_pow] at hh
  have hid : pivotLog (kappa*δ) = pivotLog δ-Real.logb 2 kappa := by
    unfold pivotLog
    rw [Real.logb_div (by norm_num : (2:ℝ) ≠ 0) (mul_ne_zero hk.ne' hδ.ne'),
      Real.logb_div (by norm_num : (2:ℝ) ≠ 0) hδ.ne',Real.logb_mul hk.ne' hδ.ne']
    ring
  have hbase : pivotLog δ = 3-Real.logb 2 δ := by
    unfold pivotLog
    rw [Real.logb_div (by norm_num : (2:ℝ) ≠ 0) hδ.ne']
    norm_num
    ring
  rw [hid,hbase]
  nlinarith [Nat.cast_nonneg (α := ℝ) q]

end
end KakeyaFormal.PivotSelectionBudgets
