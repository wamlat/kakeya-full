import PivotFourthPower
import ErrorAbsorption
import CoarseBounds
import PivotKappaScale

/-! Fixed logarithmic conditioning and finite-density errors in the actual
pivot exponents. Constants are selected before all scalar configurations. -/
namespace KakeyaFormal.PivotLossAbsorption
open PivotFourthPower
noncomputable section

/-- The log exponent from κ, marked-fraction, and explicit depth losses. -/
def totalLogLoss (a b H P Z : ℝ) : ℝ := a*H+b*P+Z

theorem totalLogLoss_nonneg {a b H P Z : ℝ}
    (ha : 0 ≤ a) (hb : 0 ≤ b) (hH : 0 ≤ H) (hP : 0 ≤ P) (hZ : 0 ≤ Z) :
    0 ≤ totalLogLoss a b H P Z := by unfold totalLogLoss; positivity

/-- Actual lower budgets can be substituted into every conditioning factor,
with the entire dependence on the common logarithm exposed. -/
theorem conditioning_lower {L kappa xi k₀ x₀ a b H P Z : ℝ}
    (hL : 0 < L) (hk₀ : 0 < k₀) (hx₀ : 0 < x₀) (hH : 0 ≤ H) (hP : 0 ≤ P)
    (hk : k₀*L^(-a) ≤ kappa) (hx : x₀*L^(-b) ≤ xi) :
    k₀^H*x₀^P*L^(-totalLogLoss a b H P Z) ≤ kappa^H*xi^P*L^(-Z) := by
  have hkpow := Real.rpow_le_rpow (by positivity : 0 ≤ k₀*L^(-a)) hk hH
  have hxpow := Real.rpow_le_rpow (by positivity : 0 ≤ x₀*L^(-b)) hx hP
  have hkpos : 0 < kappa := (by positivity : 0 < k₀*L^(-a)).trans_le hk
  have hh := mul_le_mul_of_nonneg_right
    (mul_le_mul hkpow hxpow (by positivity) (Real.rpow_nonneg hkpos.le H))
    (Real.rpow_nonneg hL.le (-Z))
  have hid : (k₀*L^(-a))^H*(x₀*L^(-b))^P*L^(-Z) =
      k₀^H*x₀^P*L^(-totalLogLoss a b H P Z) := by
    rw [Real.mul_rpow hk₀.le (Real.rpow_nonneg hL.le _),
      Real.mul_rpow hx₀.le (Real.rpow_nonneg hL.le _),
      ← Real.rpow_mul hL.le,← Real.rpow_mul hL.le]
    calc
      _ = k₀^H*x₀^P*(L^(-a*H)*L^(-b*P)*L^(-Z)) := by ring
      _ = _ := by
        rw [← Real.rpow_add hL,← Real.rpow_add hL]
        congr 2
        unfold totalLogLoss
        ring
  rwa [hid] at hh

/-- Log absorption in the physical mesh variable, uniformly for all δ≤1. -/
theorem inverse_log_delta {P eta : ℝ} (hP : 0 ≤ P) (heta : 0 < eta) :
    ∃ ell : ℝ, 0 < ell ∧ ∀ δ : ℝ, 0 < δ → δ ≤ 1 →
      ell*δ^eta ≤ (Real.log (2/δ))^(-P) := by
  obtain ⟨ell,hell,hlog⟩ := inverse_log_power_uniform_bound hP heta
  refine ⟨ell,hell,?_⟩
  intro δ hδ hδ1
  have hN : 1 ≤ δ⁻¹ := by
    have hh : (1:ℝ) ≤ 1/δ := (le_div_iff₀ hδ).mpr (by simpa only [one_mul] using hδ1)
    simpa only [one_div] using hh
  have hh := hlog δ⁻¹ hN
  rw [Real.inv_rpow hδ.le,Real.rpow_neg hδ.le,inv_inv] at hh
  simpa only [div_eq_mul_inv] using hh

/-- The base-two depth logarithm differs from the source's natural logarithm
by a fixed constant; no new δ power is needed. -/
theorem pivotLog_natural_upper {δ : ℝ} (hδ : 0 < δ) (hδ1 : δ ≤ 1) :
    PivotSelectionBudgets.pivotLog δ ≤ (3/Real.log 2)*Real.log (2/δ) := by
  have hlog2 : 0 < Real.log (2:ℝ) := Real.log_pos (by norm_num)
  have hh := Real.log_le_log (by norm_num : (0:ℝ) < 2)
    ((le_div_iff₀ hδ).mpr (by linarith) : (2:ℝ) ≤ 2/δ)
  unfold PivotSelectionBudgets.pivotLog Real.logb
  apply (mul_le_mul_iff_left₀ hlog2).mp
  have hid : (3/Real.log 2)*Real.log (2/δ)*Real.log 2 = 3*Real.log (2/δ) := by field_simp
  rw [hid]
  have hcancel : (Real.log (2/δ)/Real.log 2+2)*Real.log 2 =
      Real.log (2/δ)+2*Real.log 2 := by field_simp
  rw [hcancel]
  linarith

theorem pivotLog_inverse_power {δ P : ℝ}
    (hδ : 0 < δ) (hδ1 : δ ≤ 1) (hP : 0 ≤ P) :
    (3/Real.log 2)^(-P)*(Real.log (2/δ))^(-P) ≤ (PivotSelectionBudgets.pivotLog δ)^(-P) := by
  have hL : 0 < PivotSelectionBudgets.pivotLog δ :=
    zero_lt_one.trans_le (PivotSelectionBudgets.pivotLog_ge_one hδ hδ1)
  have hlog : 0 < Real.log (2/δ) := Real.log_pos ((lt_div_iff₀ hδ).mpr (by linarith))
  have hh := Real.rpow_le_rpow_of_nonpos hL (pivotLog_natural_upper hδ hδ1) (by linarith : -P ≤ 0)
  rwa [Real.mul_rpow (by positivity : (0:ℝ) ≤ 3/Real.log 2) hlog.le] at hh

/-- A cap-dependent total population bound still gives the required linear
inverse-cap coefficient after the fourth root. -/
theorem cap_population_linearization {A S C₀ : ℝ}
    (hA : 1 ≤ A) (hS : 0 < S) (hC : 0 < C₀) (hSC : S ≤ C₀*A) :
    C₀^(-(1/4:ℝ))*A⁻¹*S ≤ A^(-(1/4:ℝ))*S^(3/4:ℝ) := by
  have hA0 : 0 < A := zero_lt_one.trans_le hA
  have hpop := population_linearization hS hSC
  rw [Real.mul_rpow hC.le hA0.le] at hpop
  have hmul := mul_le_mul_of_nonneg_left hpop (Real.rpow_nonneg hA0.le (-(1/4:ℝ)))
  have hid : A^(-(1/4:ℝ))*(C₀^(-(1/4:ℝ))*A^(-(1/4:ℝ))*S) =
      C₀^(-(1/4:ℝ))*A^(-(1/2:ℝ))*S := by
    calc
      _ = C₀^(-(1/4:ℝ))*(A^(-(1/4:ℝ))*A^(-(1/4:ℝ)))*S := by ring
      _ = _ := by rw [← Real.rpow_add hA0]; norm_num
  rw [hid] at hmul
  have hinv : A⁻¹ ≤ A^(-(1/2:ℝ)) := by
    rw [← Real.rpow_neg_one]
    exact Real.rpow_le_rpow_of_exponent_le hA (by norm_num)
  exact (mul_le_mul_of_nonneg_right
    (mul_le_mul_of_nonneg_left hinv (Real.rpow_nonneg hC.le _)) hS.le).trans hmul

/-- Root the unconditioned fourth-power estimate with all cap factors visible. -/
theorem root_unconditioned {E c A δ lam S D C eps : ℝ}
    (hE : 0 ≤ E) (hc : 0 < c) (hA : 0 < A) (hδ : 0 < δ) (hlam : 0 < lam) (hS : 0 < S)
    (hfour : c*A⁻¹*δ^(-4*D+4*eps)*lam^(4*C)*S^3 ≤ E^4) :
    c^(1/4:ℝ)*A^(-(1/4:ℝ))*δ^(-D+eps)*lam^C*S^(3/4:ℝ) ≤ E := by
  rw [show -D+eps = (-4*D+4*eps)/4 by ring,show C = (4*C)/4 by ring,
    show -(1/4:ℝ) = (-1:ℝ)/4 by ring]
  apply le_of_pow_le_pow_left₀ (by norm_num : (4:ℕ) ≠ 0) hE
  simp only [mul_pow]
  rw [quarter_power hc.le,quarter_power hA.le,quarter_power hδ.le,quarter_power hlam.le,quarter_power hS.le]
  norm_num only [Real.rpow_one,Real.rpow_neg_one,Real.rpow_ofNat]
  exact hfour

/-- Combine the exact 3e scale error with the 2e density error and a matching
log absorption. The total fourth-power error is precisely 7e. -/
theorem density_log_fourth {E c A δ lam S D C e ell P : ℝ}
    (hc : 0 < c) (hA : 0 < A) (hδ : 0 < δ) (hlam : 0 < lam) (hS : 0 < S)
    (he : 0 ≤ e) (hell : 0 ≤ ell) (hdensity : δ/2 ≤ lam)
    (hlog : ell*δ^(2*e) ≤ (Real.log (2/δ))^(-P))
    (hfour : c*A⁻¹*δ^(-4*D+3*e)*lam^(4*C+2*e)*(Real.log (2/δ))^(-P)*S^3 ≤ E^4) :
    (c*ell*(2:ℝ)^(-2*e))*A⁻¹*δ^(-4*D+7*e)*lam^(4*C)*S^3 ≤ E^4 := by
  have hh := density_log_product hδ hlam (by linarith : 0 ≤ 2*e) hell hdensity hlog
  have hmul := mul_le_mul_of_nonneg_left hh
    (by positivity : 0 ≤ c*A⁻¹*δ^(-4*D+3*e)*lam^(4*C)*S^3)
  have hd : δ^(-4*D+7*e)=δ^(-4*D+3*e)*δ^(2*(2*e)) := by
    rw [← Real.rpow_add hδ]; congr 1; ring
  have hl : lam^(4*C+2*e)=lam^(4*C)*lam^(2*e) := Real.rpow_add hlam _ _
  have hnorm : (c*ell*(2:ℝ)^(-2*e))*A⁻¹*δ^(-4*D+7*e)*lam^(4*C)*S^3 ≤
      c*A⁻¹*δ^(-4*D+3*e)*lam^(4*C+2*e)*(Real.log (2/δ))^(-P)*S^3 := by
    rw [hd,hl,show -2*e = -(2*e) by ring]
    convert hmul using 1 <;> first | rfl | ring
  exact hnorm.trans hfour

/-- All conditioning and finite-density losses are genuinely removed, with one
constant fixed before δ, κ, ξ, λ, A, S, or E is supplied. -/
theorem uniform_absorption {D C H P Z a b k₀ x₀ C₀ c₀ e eps : ℝ}
    (hH : 0 ≤ H) (hP : 0 ≤ P) (hZ : 0 ≤ Z) (ha : 0 ≤ a) (hb : 0 ≤ b)
    (hk₀ : 0 < k₀) (hx₀ : 0 < x₀) (hC₀ : 0 < C₀) (hc₀ : 0 < c₀)
    (he : 0 < e) (herror : 7*e ≤ 4*eps) :
    ∃ c : ℝ, 0 < c ∧ ∀ δ kappa xi lam A S E : ℝ,
      0 < δ → δ ≤ 1 → 0 < lam → δ/2 ≤ lam → 1 ≤ A → 0 < S → S ≤ C₀*A → 0 ≤ E →
      k₀*(Real.log (2/δ))^(-a) ≤ kappa → x₀*(Real.log (2/δ))^(-b) ≤ xi →
      c₀*A⁻¹*kappa^H*xi^P*(Real.log (2/δ))^(-Z)*δ^(-4*D+3*e)*lam^(4*C+2*e)*S^3 ≤ E^4 →
      c*A⁻¹*δ^(-D+eps)*lam^C*S ≤ E := by
  obtain ⟨ell,hell,hlog⟩ := inverse_log_delta (totalLogLoss_nonneg ha hb hH hP hZ)
    (by linarith : 0 < 2*e)
  let cpre := c₀*k₀^H*x₀^P
  let cabs := cpre*ell*(2:ℝ)^(-2*e)
  have hcpre : 0 < cpre := by dsimp [cpre]; positivity
  have hcabs : 0 < cabs := by dsimp [cabs]; positivity
  refine ⟨cabs^(1/4:ℝ)*C₀^(-(1/4:ℝ)),by positivity,?_⟩
  intro δ kappa xi lam A S E hδ hδ1 hlam hdensity hA hS hSC hE hk hx hfour
  have hA0 : 0 < A := zero_lt_one.trans_le hA
  have hL : 0 < Real.log (2/δ) := Real.log_pos ((lt_div_iff₀ hδ).mpr (by linarith))
  have hcond := conditioning_lower (Z := Z) hL hk₀ hx₀ hH hP hk hx
  have hconditioned : cpre*A⁻¹*δ^(-4*D+3*e)*lam^(4*C+2*e)*
      (Real.log (2/δ))^(-totalLogLoss a b H P Z)*S^3 ≤ E^4 := by
    calc
      _ = (c₀*A⁻¹*δ^(-4*D+3*e)*lam^(4*C+2*e)*S^3)*
          (k₀^H*x₀^P*(Real.log (2/δ))^(-totalLogLoss a b H P Z)) := by dsimp [cpre]; ring
      _ ≤ (c₀*A⁻¹*δ^(-4*D+3*e)*lam^(4*C+2*e)*S^3)*
          (kappa^H*xi^P*(Real.log (2/δ))^(-Z)) :=
        mul_le_mul_of_nonneg_left hcond (by positivity)
      _ = c₀*A⁻¹*kappa^H*xi^P*(Real.log (2/δ))^(-Z)*δ^(-4*D+3*e)*lam^(4*C+2*e)*S^3 := by ring
      _ ≤ _ := hfour
  have habs := density_log_fourth hcpre hA0 hδ hlam hS he.le hell.le hdensity
    (hlog δ hδ hδ1) hconditioned
  have hscale := Real.rpow_le_rpow_of_exponent_ge hδ hδ1
    (by linarith : -4*D+7*e ≤ -4*D+4*eps)
  have hfinalFour : cabs*A⁻¹*δ^(-4*D+4*eps)*lam^(4*C)*S^3 ≤ E^4 := by
    refine le_trans ?_ habs
    change cabs*A⁻¹*δ^(-4*D+4*eps)*lam^(4*C)*S^3 ≤ cabs*A⁻¹*δ^(-4*D+7*e)*lam^(4*C)*S^3
    gcongr
  have hroot := root_unconditioned hE hcabs hA0 hδ hlam hS hfinalFour
  have hpop := cap_population_linearization hA hS hC₀ hSC
  calc
    _ = (cabs^(1/4:ℝ)*δ^(-D+eps)*lam^C)*(C₀^(-(1/4:ℝ))*A⁻¹*S) := by ring
    _ ≤ (cabs^(1/4:ℝ)*δ^(-D+eps)*lam^C)*(A^(-(1/4:ℝ))*S^(3/4:ℝ)) :=
      mul_le_mul_of_nonneg_left hpop (by positivity)
    _ = cabs^(1/4:ℝ)*A^(-(1/4:ℝ))*δ^(-D+eps)*lam^C*S^(3/4:ℝ) := by ring
    _ ≤ _ := hroot

/-- The lower polylogarithmic κ budget alone gives a uniform mesh threshold
for the actual twentieth-power geometric scale conditions. -/
theorem polylog_small_scales {k₀ a T : ℝ} (hk₀ : 0 < k₀) (ha : 0 ≤ a) :
    ∃ δ₀ : ℝ, 0 < δ₀ ∧ δ₀ ≤ 1 ∧ ∀ δ kappa : ℝ, 0 < δ → δ ≤ δ₀ →
      k₀*(Real.log (2/δ))^(-a) ≤ kappa → δ ≤ kappa ∧ T ≤ (1/δ)*kappa^20 := by
  obtain ⟨ell,hell,hlog⟩ := inverse_log_delta ha (by norm_num : (0:ℝ) < 1/40)
  obtain ⟨N₀,hN₀,hcut⟩ := PivotKappaScale.power_lower_cutoff (T := T)
    (mul_pos hk₀ hell)
  have hN₀pos : 0 < N₀ := zero_lt_one.trans_le hN₀
  refine ⟨1/N₀,by positivity,(div_le_one hN₀pos).mpr hN₀,?_⟩
  intro δ kappa hδ hsmall hk
  have hδ1 : δ ≤ 1 := hsmall.trans ((div_le_one hN₀pos).mpr hN₀)
  have hN : N₀ ≤ 1/δ := by
    have hh := one_div_le_one_div_of_le hδ hsmall
    simpa only [one_div_one_div] using hh
  have hpow : (1/δ)^(-(1:ℝ)/40) = δ^((1:ℝ)/40) := by
    rw [one_div,Real.inv_rpow hδ.le,show -(1:ℝ)/40 = -(1/40:ℝ) by ring,
      Real.rpow_neg hδ.le,inv_inv]
  have hbound : (k₀*ell)*(1/δ)^(-(1:ℝ)/40) ≤ kappa := by
    rw [hpow]
    calc
      _ = k₀*(ell*δ^((1:ℝ)/40)) := by ring
      _ ≤ k₀*(Real.log (2/δ))^(-a) := mul_le_mul_of_nonneg_left (hlog δ hδ hδ1) hk₀.le
      _ ≤ _ := hk
  simpa only [one_div_one_div] using hcut (1/δ) kappa hN hbound

/-- The complete uniform small-scale numeric consequence for the pivot maps.
The error is chosen first; the raw fourth-power constant may then depend on
that error, and the final threshold/constant still precede all configurations. -/
theorem pivot_small_scale_absorption (n : ℕ)
    {m d' p q k₀ x₀ a b C₀ T eps : ℝ}
    (hp : 1 ≤ p) (hq : 2 ≤ q) (hk₀ : 0 < k₀) (hx₀ : 0 < x₀)
    (ha : 0 ≤ a) (hb : 0 ≤ b) (hC₀ : 0 < C₀) (heps : 0 < eps) :
    ∃ e : ℝ, 0 < e ∧ e ≤ 1 ∧ ∀ c₀ : ℝ, 0 < c₀ →
      ∃ δ₀ c : ℝ, 0 < δ₀ ∧ δ₀ ≤ 1 ∧ 0 < c ∧
      ∀ δ kappa xi lam A S E : ℝ,
      0 < δ → δ ≤ δ₀ → 0 < lam → δ/2 ≤ lam → 1 ≤ A → 0 < S → S ≤ C₀*A → 0 ≤ E →
      k₀*(Real.log (2/δ))^(-a) ≤ kappa → x₀*(Real.log (2/δ))^(-b) ≤ xi →
      δ ≤ kappa ∧ T ≤ (1/δ)*kappa^20 ∧
      (c₀*A⁻¹*kappa^(5*(n:ℝ)+6*q+12)*xi^(p+3)*(Real.log (2/δ))^(-(p+4))*
        δ^(-2*m-3-d'+3*e)*lam^(p+2*q+4+2*e)*S^3 ≤ E^4 →
        c*A⁻¹*δ^(-KakeyaScalar.pivotSet m d'+eps)*lam^(KakeyaScalar.pivotDensity p q)*S ≤ E) := by
  let e := min (1/2:ℝ) (eps/4)
  have he : 0 < e := lt_min (by norm_num) (by positivity)
  have he1 : e ≤ 1 := (min_le_left _ _).trans (by norm_num)
  have herror : 7*e ≤ 4*eps := by have := min_le_right (1/2:ℝ) (eps/4); dsimp [e]; linarith
  refine ⟨e,he,he1,?_⟩
  intro c₀ hc₀
  obtain ⟨c,hc,hbound⟩ := uniform_absorption
    (D := KakeyaScalar.pivotSet m d') (C := KakeyaScalar.pivotDensity p q)
    (H := 5*(n:ℝ)+6*q+12) (P := p+3) (Z := p+4)
    (by positivity : 0 ≤ 5*(n:ℝ)+6*q+12) (by linarith : 0 ≤ p+3) (by linarith : 0 ≤ p+4)
    ha hb hk₀ hx₀ hC₀ hc₀ he herror
  obtain ⟨δ₀,hδ₀,hδ₀1,hscale⟩ := polylog_small_scales (T := T) hk₀ ha
  refine ⟨δ₀,c,hδ₀,hδ₀1,hc,?_⟩
  intro δ kappa xi lam A S E hδ hδsmall hlam hdensity hA hS hSC hE hk hx
  obtain ⟨hδk,h20⟩ := hscale δ kappa hδ hδsmall hk
  refine ⟨hδk,h20,?_⟩
  intro hfour
  apply hbound δ kappa xi lam A S E hδ (hδsmall.trans hδ₀1) hlam hdensity hA hS hSC hE hk hx
  have hd : -4*KakeyaScalar.pivotSet m d'+3*e = -2*m-3-d'+3*e := by unfold KakeyaScalar.pivotSet; ring
  have hl : 4*KakeyaScalar.pivotDensity p q+2*e = p+2*q+4+2*e := by unfold KakeyaScalar.pivotDensity; ring
  simpa only [hd,hl] using hfour

/-- The population budget is already supplied by the actual real-cap geometry,
including a varying cap coefficient A. -/
theorem configuration_population_bound {k : ℕ} {m : ℝ}
    (geom : Normalization) (F : ShadedConfiguration (k+1) geom m) :
    (F.M:ℝ)*F.δ^m ≤ ProjectiveGeometry.packingConstant k*F.A := by
  have hA : 0 < F.A := zero_lt_one.trans_le F.cap_ge_one
  have hh := CapCover.cap_bound_total_count_scale F.family F.scale_pos F.scale_le_one hA.le F.cap_bound
  have hpow : 0 < F.δ^m := Real.rpow_pos_of_pos F.scale_pos m
  have hmul := mul_le_mul_of_nonneg_right hh hpow.le
  have hid : (ProjectiveGeometry.packingConstant k*F.A*F.δ^(-m))*F.δ^m =
      ProjectiveGeometry.packingConstant k*F.A := by
    rw [Real.rpow_neg F.scale_pos.le]
    field_simp
  rwa [hid] at hmul

/-- Configuration-facing small-scale consequence. Density and total-population
budgets are derived from the actual finite configuration, not assumed. The
remaining hypotheses are the conditioning budgets and concrete E⁴ inequality. -/
theorem configuration_absorption (k : ℕ)
    {m d' p q k₀ x₀ a b T eps : ℝ}
    (hp : 1 ≤ p) (hq : 2 ≤ q) (hk₀ : 0 < k₀) (hx₀ : 0 < x₀)
    (ha : 0 ≤ a) (hb : 0 ≤ b) (heps : 0 < eps) :
    ∃ e : ℝ, 0 < e ∧ e ≤ 1 ∧ ∀ c₀ : ℝ, 0 < c₀ →
      ∃ δ₀ c : ℝ, 0 < δ₀ ∧ δ₀ ≤ 1 ∧ 0 < c ∧
      ∀ (geom : Normalization) (F : ShadedConfiguration (k+1) geom m) (kappa xi : ℝ),
      0 < F.M → F.δ ≤ δ₀ →
      k₀*(Real.log (2/F.δ))^(-a) ≤ kappa → x₀*(Real.log (2/F.δ))^(-b) ≤ xi →
      (c₀*F.A⁻¹*kappa^(5*(k:ℝ)+6*q+12)*xi^(p+3)*(Real.log (2/F.δ))^(-(p+4))*
        F.δ^(-2*m-3-d'+3*e)*F.lam^(p+2*q+4+2*e)*((F.M:ℝ)*F.δ^m)^3 ≤
          (F.family.unionCells.card:ℝ)^4) →
      c*F.A⁻¹*F.δ^(m-KakeyaScalar.pivotSet m d'+eps)*
        F.lam^(KakeyaScalar.pivotDensity p q)*F.M ≤ (F.family.unionCells.card:ℝ) := by
  have hC₀ : 0 < ProjectiveGeometry.packingConstant k :=
    zero_lt_one.trans_le (ProjectiveGeometry.packingConstant_ge_one k)
  obtain ⟨e,he,he1,hchoose⟩ := pivot_small_scale_absorption k
    (m := m) (d' := d') (T := T) hp hq hk₀ hx₀ ha hb hC₀ heps
  refine ⟨e,he,he1,?_⟩
  intro c₀ hc₀
  obtain ⟨δ₀,c,hδ₀,hδ₀1,hc,hbound⟩ := hchoose c₀ hc₀
  refine ⟨δ₀,c,hδ₀,hδ₀1,hc,?_⟩
  intro geom F kappa xi hM hscale hk hx hfour
  have hMpos : (0:ℝ) < F.M := by exact_mod_cast hM
  have hS : 0 < (F.M:ℝ)*F.δ^m := by positivity [F.scale_pos]
  have hh := (hbound F.δ kappa xi F.lam F.A ((F.M:ℝ)*F.δ^m)
    (F.family.unionCells.card:ℝ) F.scale_pos hscale F.density_pos
    (F.density_ge_half_scale hM) F.cap_ge_one hS (configuration_population_bound geom F)
    (Nat.cast_nonneg _) hk hx).2.2 hfour
  have hid : F.δ^(m-KakeyaScalar.pivotSet m d'+eps) =
      F.δ^(-KakeyaScalar.pivotSet m d'+eps)*F.δ^m := by
    rw [← Real.rpow_add F.scale_pos]
    congr 1
    ring
  rw [hid]
  convert hh using 1
  ring

end
end KakeyaFormal.PivotLossAbsorption
