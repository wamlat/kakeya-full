import AnisotropicSamplingInput

/-! Fixed logarithmic budgets for the actual constants returned by
`AnisotropicSamplingInput`. This module changes no selected family or shading.
The measured selection supplies its depth and retention inequalities; the
results below account for all their logarithmic costs explicitly. -/
namespace KakeyaFormal.AnisotropicSamplingBudgets
open AnisotropicSamplingInput AnisotropicJointRecovery
noncomputable section

/-- Positive even when the fixed lower coefficient exceeds one. -/
def depthCoefficient (e₀ q : ℝ) : ℝ :=
  (|Real.log (4/e₀)|+q)/Real.log 2+2

def markedCoefficient (e₀ q : ℝ) : ℝ := e₀/(4*depthCoefficient e₀ q)
def endsCoefficient (B₀ e₀ : ℝ) : ℝ := 4*B₀/e₀
def broadCoefficient (angular beta K₀ e₀ q : ℝ) : ℝ :=
  8*depthCoefficient e₀ q*broadFactor angular beta K₀/e₀

theorem depthCoefficient_pos {e₀ q : ℝ} (hq : 0 ≤ q) :
    0 < depthCoefficient e₀ q := by
  unfold depthCoefficient
  have hlog : 0 < Real.log 2 := Real.log_pos (by norm_num)
  positivity

theorem inverse_retention {e₀ L q e : ℝ} (he₀ : 0 < e₀) (hL : 0 < L)
    (_he : 0 < e) (hbudget : e₀*L^(-q) ≤ e) :
    e⁻¹ ≤ e₀⁻¹*L^q := by
  have hp : 0 < e₀*L^(-q) := mul_pos he₀ (Real.rpow_pos_of_pos hL _)
  have hh := inv_anti₀ hp hbudget
  simpa only [mul_inv_rev,Real.rpow_neg hL.le,inv_inv,mul_comm] using hh

/-- The actual logarithmic density-selection depth has a fixed linear-log budget. -/
theorem depth_bound {e₀ L q e : ℝ} {D : ℕ} (he₀ : 0 < e₀) (hq : 0 ≤ q)
    (hL : 1 ≤ L) (he : 0 < e) (hbudget : e₀*L^(-q) ≤ e)
    (hdepth : (D:ℝ)+1 ≤ Real.log (4/e)/Real.log 2+2) :
    (D:ℝ)+1 ≤ depthCoefficient e₀ q*L := by
  have hLp : 0 < L := zero_lt_one.trans_le hL
  have hlog2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hi := inverse_retention he₀ hLp he hbudget
  have hratio : 4/e ≤ (4/e₀)*L^q := by
    simpa only [div_eq_mul_inv,mul_assoc] using mul_le_mul_of_nonneg_left hi (by norm_num : (0:ℝ)≤4)
  have hlog := Real.log_le_log (div_pos (by norm_num) he) hratio
  rw [Real.log_mul (div_pos (by norm_num) he₀).ne' (Real.rpow_pos_of_pos hLp q).ne',
    Real.log_rpow hLp] at hlog
  have hlogL : Real.log L ≤ L := (Real.log_le_sub_one_of_pos hLp).trans (by linarith)
  have hmain : Real.log (4/e) ≤ (|Real.log (4/e₀)|+q)*L := by
    have habs : Real.log (4/e₀) ≤ |Real.log (4/e₀)| := le_abs_self _
    have hmul : |Real.log (4/e₀)| ≤ |Real.log (4/e₀)| * L :=
      le_mul_of_one_le_right (abs_nonneg _) hL
    nlinarith [mul_le_mul_of_nonneg_left hlogL hq]
  have hdiv := div_le_div_of_nonneg_right hmain hlog2.le
  calc
    _ ≤ Real.log (4/e)/Real.log 2+2 := hdepth
    _ ≤ (|Real.log (4/e₀)|+q)*L/Real.log 2+2*L := add_le_add hdiv (by linarith)
    _ = _ := by unfold depthCoefficient; ring

theorem per_depth_retention {e₀ L q e : ℝ} {D : ℕ}
    (he₀ : 0 < e₀) (hq : 0 ≤ q) (hL : 0 < L)
    (hbudget : e₀*L^(-q) ≤ e)
    (hdepth : (D:ℝ)+1 ≤ depthCoefficient e₀ q*L) :
    (e₀/depthCoefficient e₀ q)*L^(-(q+1)) ≤ e/(D+1:ℕ) := by
  have hc := depthCoefficient_pos (e₀:=e₀) hq
  have hD : (0:ℝ) < (D+1:ℕ) := by positivity
  have hd : ((D+1:ℕ):ℝ) ≤ depthCoefficient e₀ q*L := by simpa using hdepth
  have hh : e₀*L^(-q)/(depthCoefficient e₀ q*L) ≤ e/(D+1:ℕ) :=
    (div_le_div_of_nonneg_left (by positivity) hD hd).trans
      (div_le_div_of_nonneg_right hbudget hD.le)
  convert hh using 1
  rw [show -(q+1) = -q + -1 by ring,Real.rpow_add hL,Real.rpow_neg_one]
  field_simp

theorem marked_budget {e₀ L q e : ℝ} {D : ℕ}
    (he₀ : 0 < e₀) (hq : 0 ≤ q) (hL : 0 < L)
    (hbudget : e₀*L^(-q) ≤ e)
    (hdepth : (D:ℝ)+1 ≤ depthCoefficient e₀ q*L) :
    markedCoefficient e₀ q*L^(-(q+1)) ≤ markedFraction e D := by
  have hh := div_le_div_of_nonneg_right (per_depth_retention he₀ hq hL hbudget hdepth)
    (by norm_num : (0:ℝ)≤4)
  dsimp only [markedCoefficient,markedFraction]
  convert hh using 1 <;> first | rfl | ring

theorem ends_budget {e₀ L q e B B₀ b : ℝ}
    (he₀ : 0 < e₀) (hL : 0 < L) (he : 0 < e) (hB₀ : 0 ≤ B₀)
    (hbudget : e₀*L^(-q) ≤ e) (hB : B ≤ B₀*L^b) :
    endsConstant B e ≤ endsCoefficient B₀ e₀*L^(b+q) := by
  have hi := inverse_retention he₀ hL he hbudget
  have h1 := mul_le_mul_of_nonneg_right hB (by positivity : (0:ℝ)≤4/e)
  have h2 := mul_le_mul_of_nonneg_left hi (by positivity : (0:ℝ)≤4*(B₀*L^b))
  apply h1.trans
  convert h2 using 1 <;>
    simp only [endsCoefficient,Real.rpow_add hL,div_eq_mul_inv] <;> ring

theorem broad_budget {e₀ L q e angular beta K K₀ kLog : ℝ} {D : ℕ}
    (he₀ : 0 < e₀) (hq : 0 ≤ q) (hL : 0 < L) (he : 0 < e)
    (hK₀ : 0 ≤ K₀) (hbudget : e₀*L^(-q) ≤ e)
    (hdepth : (D:ℝ)+1 ≤ depthCoefficient e₀ q*L) (hK : K ≤ K₀*L^kLog) :
    broadConstant angular beta K e D ≤
      broadCoefficient angular beta K₀ e₀ q*L^(kLog+q+1) := by
  have hc := depthCoefficient_pos (e₀:=e₀) hq
  have hg : 0 ≤ (8*(1+2*angular)^2)^beta := Real.rpow_nonneg (by positivity) _
  have hi := inverse_retention he₀ hL he hbudget
  have hd : ((D+1:ℕ):ℝ) ≤ depthCoefficient e₀ q*L := by simpa using hdepth
  have h1 := mul_le_mul_of_nonneg_right hK
    (by positivity : (0:ℝ)≤(8*(1+2*angular)^2)^beta*(8*(D+1:ℕ)/e))
  have h2 := mul_le_mul_of_nonneg_left hd
    (by positivity : (0:ℝ)≤(K₀*L^kLog)*(8*(1+2*angular)^2)^beta*8/e)
  have h3 := mul_le_mul_of_nonneg_left hi
    (by positivity : (0:ℝ)≤(K₀*L^kLog)*(8*(1+2*angular)^2)^beta*8*(depthCoefficient e₀ q*L))
  calc
    _ ≤ (K₀*L^kLog)*(8*(1+2*angular)^2)^beta*(8*(D+1:ℕ)/e) := by
      simpa only [broadConstant,broadFactor,mul_assoc] using h1
    _ ≤ (K₀*L^kLog)*(8*(1+2*angular)^2)^beta*8/e*(depthCoefficient e₀ q*L) := by
      convert h2 using 1 <;> first | rfl | ring
    _ ≤ (K₀*L^kLog)*(8*(1+2*angular)^2)^beta*8*(depthCoefficient e₀ q*L)*(e₀⁻¹*L^q) := by
      convert h3 using 1 <;> first | rfl | ring
    _ = _ := by
      simp only [broadCoefficient,broadFactor,Real.rpow_add hL,Real.rpow_one,div_eq_mul_inv]
      ring

theorem coefficients_pos {e₀ q angular beta B₀ K₀ : ℝ}
    (he₀ : 0 < e₀) (hq : 0 ≤ q) (ha : 0 ≤ angular)
    (hB₀ : 0 < B₀) (hK₀ : 0 < K₀) :
    0 < depthCoefficient e₀ q ∧ 0 < markedCoefficient e₀ q ∧
      0 < endsCoefficient B₀ e₀ ∧ 0 < broadCoefficient angular beta K₀ e₀ q := by
  have hc := depthCoefficient_pos (e₀:=e₀) hq
  have hg : 0 < (8*(1+2*angular)^2)^beta := Real.rpow_pos_of_pos (by positivity) _
  exact ⟨hc,div_pos he₀ (by positivity),div_pos (by positivity) he₀,
    div_pos (mul_pos (mul_pos (by norm_num) hc) (mul_pos hK₀ hg)) he₀⟩

/-- Segment and separation-color costs change only the fixed lower coefficient. -/
theorem retention_budget (k : ℕ) (angular : ℝ) {eta eta₀ L q : ℝ}
    (hbudget : eta₀*L^(-q) ≤ eta) :
    retention k angular eta₀*L^(-q) ≤ retention k angular eta := by
  have hN : (0:ℝ) < AnisotropicShading.segmentCount angular :=
    Nat.cast_pos.mpr (AnisotropicShading.segmentCount_pos angular)
  have hP : (0:ℝ) < SeparationColoring.paletteSize k (AnisotropicJointGeometry.separationFactor angular) :=
    Nat.cast_pos.mpr (SeparationColoring.paletteSize_pos _ _)
  have hh := div_le_div_of_nonneg_right hbudget (mul_pos hN hP).le
  convert hh using 1 <;> first | rfl | (unfold retention; ring)

theorem density_retention {e₀ L q e lam lamNew : ℝ}
    (hlam : 0 ≤ lam) (hbudget : e₀*L^(-q) ≤ e)
    (hdensity : e*lam/4 ≤ lamNew) :
    (e₀/4)*L^(-q)*lam ≤ lamNew := by
  have hh := div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_right hbudget hlam)
    (by norm_num : (0:ℝ)≤4)
  apply le_trans ?_ hdensity
  convert hh using 1
  ring

theorem population_retention {e₀ L q e M Mnew : ℝ} {D : ℕ}
    (he₀ : 0 < e₀) (hq : 0 ≤ q) (hL : 0 < L) (hM : 0 ≤ M)
    (hbudget : e₀*L^(-q) ≤ e)
    (hdepth : (D:ℝ)+1 ≤ depthCoefficient e₀ q*L)
    (hpopulation : e*M/(16*(D+1:ℕ)) ≤ Mnew) :
    (e₀/(16*depthCoefficient e₀ q))*L^(-(q+1))*M ≤ Mnew := by
  have hh := div_le_div_of_nonneg_right
    (mul_le_mul_of_nonneg_right (per_depth_retention he₀ hq hL hbudget hdepth) hM)
    (by norm_num : (0:ℝ)≤16)
  apply le_trans ?_ hpopulation
  convert hh using 1 <;> first | rfl | ring

/-- The stronger retained density-times-population bound avoids multiplying
two separate retention losses. -/
theorem density_population_retention {e₀ L q e lam M lamNew Mnew : ℝ} {D : ℕ}
    (he₀ : 0 < e₀) (hq : 0 ≤ q) (hL : 0 < L) (hlam : 0 ≤ lam) (hM : 0 ≤ M)
    (hbudget : e₀*L^(-q) ≤ e)
    (hdepth : (D:ℝ)+1 ≤ depthCoefficient e₀ q*L)
    (hpopulation : e*lam*M/(16*(D+1:ℕ)) ≤ lamNew*Mnew) :
    (e₀/(16*depthCoefficient e₀ q))*L^(-(q+1))*lam*M ≤ lamNew*Mnew := by
  have hh := population_retention he₀ hq hL (mul_nonneg hlam hM) hbudget hdepth
    (by simpa only [mul_assoc] using hpopulation)
  simpa only [mul_assoc] using hh

/-- All transformed constants are fixed before the actual log, retention,
depth, and original two-ends/broadness constants are chosen. -/
theorem uniform_constants (e₀ q angular beta B₀ K₀ bLog kLog : ℝ)
    (he₀ : 0 < e₀) (hq : 0 ≤ q) (ha : 0 ≤ angular)
    (hB₀ : 0 < B₀) (hK₀ : 0 < K₀) :
    ∃ Cdepth xi₀ Bnew₀ Knew₀ : ℝ,
      0 < Cdepth ∧ 0 < xi₀ ∧ 0 < Bnew₀ ∧ 0 < Knew₀ ∧
      ∀ {L e B K : ℝ} {D : ℕ}, 1 ≤ L → 0 < e → e₀*L^(-q) ≤ e →
      (D:ℝ)+1 ≤ Real.log (4/e)/Real.log 2+2 →
      B ≤ B₀*L^bLog → K ≤ K₀*L^kLog →
      (D:ℝ)+1 ≤ Cdepth*L ∧ xi₀*L^(-(q+1)) ≤ markedFraction e D ∧
      endsConstant B e ≤ Bnew₀*L^(bLog+q) ∧
      broadConstant angular beta K e D ≤ Knew₀*L^(kLog+q+1) := by
  obtain ⟨hc,hxi,hB,hK⟩ := coefficients_pos (beta:=beta) he₀ hq ha hB₀ hK₀
  refine ⟨depthCoefficient e₀ q,markedCoefficient e₀ q,endsCoefficient B₀ e₀,
    broadCoefficient angular beta K₀ e₀ q,hc,hxi,hB,hK,?_⟩
  intro L e B K D hL he hbudget hdepth hBbudget hKbudget
  have hLp := zero_lt_one.trans_le hL
  have hd := depth_bound he₀ hq hL he hbudget hdepth
  exact ⟨hd,marked_budget he₀ hq hLp hbudget hd,
    ends_budget he₀ hLp he hB₀.le hbudget hBbudget,
    broad_budget he₀ hq hLp he hK₀.le hbudget hd hKbudget⟩

end
end KakeyaFormal.AnisotropicSamplingBudgets
