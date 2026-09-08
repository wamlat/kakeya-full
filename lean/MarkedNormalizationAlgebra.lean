import MarkedNormalizationKappa

/-! Fixed parameter transport from the common refined grid back to the
original scale, density, marked fraction and occupied-cell population. -/
namespace KakeyaFormal.MarkedNormalizationAlgebra
noncomputable section

def logFactor (q : ℝ) : ℝ := 1+Real.log q/Real.log 2

theorem logFactor_ge_one {q : ℝ} (hq : 1 ≤ q) : 1 ≤ logFactor q := by
  have hlog : 0 ≤ Real.log q := Real.log_nonneg hq
  have htwo : 0 < Real.log (2:ℝ) := Real.log_pos (by norm_num)
  unfold logFactor
  have hh := div_nonneg hlog htwo.le
  linarith

theorem refined_log_upper {δ q : ℝ} (hδ : 0 < δ) (hδ1 : δ ≤ 1) (hq : 1 ≤ q) :
    Real.log (2/(δ/q)) ≤ logFactor q*Real.log (2/δ) := by
  have hq0 : 0 < q := by linarith
  have htwo : 0 < Real.log (2:ℝ) := Real.log_pos (by norm_num)
  have hlogq : 0 ≤ Real.log q := Real.log_nonneg hq
  have hL : Real.log (2:ℝ) ≤ Real.log (2/δ) := by
    apply Real.log_le_log (by norm_num)
    apply (le_div_iff₀ hδ).mpr
    linarith
  have hid : (2:ℝ)/(δ/q)=(2/δ)*q := by field_simp
  rw [hid,Real.log_mul (by positivity : (2:ℝ)/δ ≠ 0) hq0.ne']
  have hh := mul_le_mul_of_nonneg_left hL (div_nonneg hlogq htwo.le)
  have heq : (Real.log q/Real.log 2)*Real.log 2=Real.log q := by field_simp
  rw [heq] at hh
  unfold logFactor
  nlinarith

theorem refined_log_power {δ q Z : ℝ} (hδ : 0 < δ) (hδ1 : δ ≤ 1) (hq : 1 ≤ q) (hZ : 0 ≤ Z) :
    (logFactor q)^(-Z)*(Real.log (2/δ))^(-Z) ≤ (Real.log (2/(δ/q)))^(-Z) := by
  have hq0 : 0 < q := by linarith
  have hnew : δ/q ≤ 1 := (div_le_one hq0).mpr (hδ1.trans hq)
  have hnew0 : 0 < δ/q := div_pos hδ hq0
  have hLn : 0 < Real.log (2/(δ/q)) := by
    apply Real.log_pos
    apply (one_lt_div hnew0).mpr
    linarith
  have hh := Real.rpow_le_rpow_of_nonpos hLn (refined_log_upper hδ hδ1 hq) (neg_nonpos.mpr hZ)
  rw [Real.mul_rpow (zero_le_one.trans (logFactor_ge_one hq)) (by
    apply Real.log_nonneg
    apply (one_le_div hδ).mpr
    linarith)] at hh
  exact hh

theorem scale_identity {δ q M U m : ℝ} (hδ : 0 ≤ δ) (hq : 0 ≤ q) :
    (δ/q)^U*(M*(δ/q)^m)^3=
      (q⁻¹)^U*((q⁻¹)^m)^3*(δ^U*(M*δ^m)^3) := by
  rw [div_eq_mul_inv,Real.mul_rpow hδ (inv_nonneg.mpr hq),Real.mul_rpow hδ (inv_nonneg.mpr hq)]
  ring

def transportFactor (n : ℕ) (q b D X Z U V m : ℝ) : ℝ :=
  (D⁻¹)^X*(logFactor q)^(-Z)*(q⁻¹)^U*(b/q)^V*((q⁻¹)^m)^3/(q^n)^4

theorem transportFactor_pos (n : ℕ) {q b D X Z U V m : ℝ}
    (hq : 1 ≤ q) (hb : 0 < b) (hD : 0 < D) :
    0 < transportFactor n q b D X Z U V m := by
  have hq0 : 0 < q := by linarith
  have hlog := zero_lt_one.trans_le (logFactor_ge_one hq)
  unfold transportFactor
  positivity

/-- Simultaneous transport of all powers, with arbitrary real scale exponent.
The only monotonic density exponent requirement is V≥0. -/
theorem transport_fourth (n : ℕ) {c A kap xi δ lam nu M E q b D H X Z U V m : ℝ}
    (hc : 0 ≤ c) (hA : 0 < A) (hk : 0 < kap) (hxi : 0 < xi)
    (hδ : 0 < δ) (hδ1 : δ ≤ 1) (hlam : 0 < lam) (hM : 0 ≤ M)
    (hq : 1 ≤ q) (hb : 0 < b) (hD : 0 < D) (hZ : 0 ≤ Z) (hV : 0 ≤ V)
    (hnu : (b/q)*lam ≤ nu)
    (hfour : c*A⁻¹*kap^H*(xi/D)^X*(Real.log (2/(δ/q)))^(-Z)*(δ/q)^U*
      nu^V*(M*(δ/q)^m)^3 ≤ (q^n*E)^4) :
    (c*transportFactor n q b D X Z U V m)*A⁻¹*kap^H*xi^X*
      (Real.log (2/δ))^(-Z)*δ^U*lam^V*(M*δ^m)^3 ≤ E^4 := by
  have hq0 : 0 < q := by linarith
  have hLp : 0 < Real.log (2/δ) := by
    apply Real.log_pos
    apply (one_lt_div hδ).mpr
    linarith
  have hLn : 0 < Real.log (2/(δ/q)) := by
    apply Real.log_pos
    apply (one_lt_div (div_pos hδ hq0)).mpr
    have hh : δ/q ≤ 1 := (div_le_one hq0).mpr (hδ1.trans hq)
    linarith
  have hlog := refined_log_power hδ hδ1 hq hZ
  have hden : 0 < (q^n)^4 := by positivity
  have hnu0 : 0 < nu := (mul_pos (div_pos hb hq0) hlam).trans_le hnu
  have hlamp := Real.rpow_le_rpow (by positivity : 0 ≤ (b/q)*lam) hnu hV
  rw [Real.mul_rpow (by positivity : 0 ≤ b/q) hlam.le] at hlamp
  have hmark : (xi/D)^X=(D⁻¹)^X*xi^X := by
    rw [div_eq_mul_inv,Real.mul_rpow hxi.le (by positivity)]
    ring
  have hscale := scale_identity (M := M) (U := U) (m := m) hδ.le hq0.le
  have hcompare :
      c*A⁻¹*kap^H*((D⁻¹)^X*xi^X)*((logFactor q)^(-Z)*(Real.log (2/δ))^(-Z))*
      ((q⁻¹)^U*((q⁻¹)^m)^3*(δ^U*(M*δ^m)^3))*((b/q)^V*lam^V) ≤
      c*A⁻¹*kap^H*(xi/D)^X*(Real.log (2/(δ/q)))^(-Z)*(δ/q)^U*nu^V*(M*(δ/q)^m)^3 := by
    calc
      _ ≤ c*A⁻¹*kap^H*((D⁻¹)^X*xi^X)*(Real.log (2/(δ/q)))^(-Z)*
          ((q⁻¹)^U*((q⁻¹)^m)^3*(δ^U*(M*δ^m)^3))*nu^V := by gcongr
      _ = _ := by rw [← hmark,← hscale]; ring
  have hbound := hcompare.trans hfour
  have hfinal := div_le_div_of_nonneg_right hbound hden.le
  have hright : (q^n*E)^4/(q^n)^4=E^4 := by
    rw [mul_pow]
    field_simp
  apply le_of_eq_of_le ?_ (hfinal.trans_eq hright)
  unfold transportFactor
  ring

end
end KakeyaFormal.MarkedNormalizationAlgebra
