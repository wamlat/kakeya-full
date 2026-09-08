import PivotLossAbsorption

/-! Scalar composition of Proposition 8.1. The set exponent remains D,
while the density exponent becomes max D C. These results do not construct
localized families, cap thinning, or the spatial disjoint-union summation. -/
namespace KakeyaFormal.TwoEndsGlobalizationAlgebra
noncomputable section

def densityExponent (D C : ℝ) : ℝ := max D C
def geometryCoefficient (G D C : ℝ) : ℝ := G^(-(max (D-C) 0))

theorem geometryCoefficient_pos {G D C : ℝ} (hG : 0 < G) :
    0 < geometryCoefficient G D C := Real.rpow_pos_of_pos hG _

/-- The exact power identity after thinning by rho^m and isotropic rescaling. -/
theorem localized_scaling_identity {δ rho nu m D C eta : ℝ}
    (hδ : 0 < δ) (hrho : 0 < rho) (hnu : 0 < nu) :
    (δ/rho)^(m-D+eta)*(nu/rho)^C*rho^m =
      δ^(m-D+eta)*nu^C*rho^(D-C-eta) := by
  rw [Real.div_rpow hδ.le hrho.le,Real.div_rpow hnu.le hrho.le]
  rw [div_eq_mul_inv,div_eq_mul_inv,← Real.rpow_neg hrho.le,← Real.rpow_neg hrho.le]
  calc
    _ = δ^(m-D+eta)*nu^C*(rho^(-(m-D+eta))*rho^(-C)*rho^m) := by ring
    _ = _ := by
      rw [← Real.rpow_add hrho,← Real.rpow_add hrho]
      congr 2
      ring

/-- Discarding the extra nonnegative scale loss uses rho≤1 in this direction. -/
theorem localized_scale_loss {δ rho nu m D C eta : ℝ}
    (hδ : 0 < δ) (hrho : 0 < rho) (hrho1 : rho ≤ 1)
    (hnu : 0 < nu) (heta : 0 ≤ eta) :
    δ^(m-D+eta)*nu^C*rho^(D-C) ≤
      (δ/rho)^(m-D+eta)*(nu/rho)^C*rho^m := by
  rw [localized_scaling_identity hδ hrho hnu]
  exact mul_le_mul_of_nonneg_left
    (Real.rpow_le_rpow_of_exponent_ge hrho hrho1 (by linarith)) (by positivity)

/-- The geometric upper bound on old density raises the density exponent
to max(D,C), with an explicit fixed coefficient. -/
theorem density_collapse {rho nu G D C : ℝ}
    (hrho : 0 < rho) (hrho1 : rho ≤ 1) (hnu : 0 < nu)
    (hG : 1 ≤ G) (hupper : nu ≤ G*rho) :
    geometryCoefficient G D C*nu^(densityExponent D C) ≤ nu^C*rho^(D-C) := by
  have hGp : 0 < G := zero_lt_one.trans_le hG
  by_cases hCD : C ≤ D
  · have hdiv : nu/G ≤ rho := (div_le_iff₀ hGp).mpr (by nlinarith [hupper])
    have hpow := Real.rpow_le_rpow (div_pos hnu hGp).le hdiv
      (by linarith : 0 ≤ D-C)
    rw [Real.div_rpow hnu.le hGp.le] at hpow
    have hh := mul_le_mul_of_nonneg_left hpow (Real.rpow_nonneg hnu.le C)
    have hnuD : nu^D = nu^C*nu^(D-C) := by
      rw [← Real.rpow_add hnu]
      congr 1
      ring
    calc
      _ = nu^C*(nu^(D-C)/G^(D-C)) := by
        rw [densityExponent,max_eq_left hCD,geometryCoefficient,max_eq_left (by linarith),
          Real.rpow_neg hGp.le,hnuD]
        ring
      _ ≤ _ := hh
  · have hDC : D ≤ C := le_of_not_ge hCD
    have hpow : (1:ℝ) ≤ rho^(D-C) := by
      simpa only [Real.rpow_zero] using
        Real.rpow_le_rpow_of_exponent_ge hrho hrho1 (by linarith : D-C ≤ 0)
    simpa only [densityExponent,max_eq_right hDC,geometryCoefficient,
      max_eq_right (by linarith : D-C ≤ 0),neg_zero,Real.rpow_zero,one_mul,mul_one] using
      mul_le_mul_of_nonneg_left hpow (Real.rpow_nonneg hnu.le C)

/-- The localized density lower budget, including its full logarithmic power. -/
theorem density_lower {δ rho nu lam cNu L a alpha P : ℝ}
    (hδ : 0 < δ) (hrho : δ ≤ rho) (hlam : 0 < lam)
    (hcNu : 0 < cNu) (hL : 0 < L) (halpha : 0 ≤ alpha) (hP : 0 ≤ P)
    (hlower : cNu*L^(-a)*rho^alpha*lam ≤ nu) :
    cNu^P*L^(-(a*P))*δ^(alpha*P)*lam^P ≤ nu^P := by
  have hrhop : 0 < rho := hδ.trans_le hrho
  have hpow := Real.rpow_le_rpow (by positivity : 0 ≤ cNu*L^(-a)*rho^alpha*lam) hlower hP
  have hscale := Real.rpow_le_rpow hδ.le hrho (mul_nonneg halpha hP)
  have hnorm : (cNu*L^(-a)*rho^alpha*lam)^P =
      cNu^P*L^(-(a*P))*rho^(alpha*P)*lam^P := by
    simp only [Real.mul_rpow (by positivity : (0:ℝ)≤cNu*L^(-a)*rho^alpha) hlam.le,
      Real.mul_rpow (by positivity : (0:ℝ)≤cNu*L^(-a)) (Real.rpow_nonneg hrhop.le alpha),
      Real.mul_rpow hcNu.le (Real.rpow_nonneg hL.le (-a)),
      ← Real.rpow_mul hL.le,← Real.rpow_mul hrhop.le,neg_mul]
  rw [hnorm] at hpow
  exact (mul_le_mul_of_nonneg_right
    (mul_le_mul_of_nonneg_left hscale (by positivity)) (Real.rpow_nonneg hlam.le P)).trans hpow

/-- Fixed loss allocation leaves strictly positive room for all logarithms.
It precedes the choice of constants supplied by the two-ends estimate. -/
theorem choose_losses {D C eps : ℝ} (hD : 1 ≤ D) (_hC : 1 ≤ C) (heps : 0 < eps) :
    ∃ alpha eta : ℝ, 0 < alpha ∧ alpha < 1 ∧ 0 < eta ∧
      eta+alpha*densityExponent D C < eps := by
  have hP : 0 < densityExponent D C := zero_lt_one.trans_le (hD.trans (le_max_left _ _))
  let alpha := min (1/2:ℝ) (eps/(4*densityExponent D C))
  have ha : 0 < alpha := lt_min (by norm_num) (div_pos heps (by positivity))
  have ha1 : alpha < 1 := (min_le_left _ _).trans_lt (by norm_num)
  have hap : alpha*densityExponent D C ≤ eps/4 := by
    have hh := mul_le_mul_of_nonneg_right (min_le_right (1/2:ℝ) (eps/(4*densityExponent D C))) hP.le
    have hid : eps/(4*densityExponent D C)*densityExponent D C = eps/4 := by field_simp
    exact hh.trans_eq hid
  exact ⟨alpha,eps/4,ha,ha1,by positivity,by linarith⟩

/-- The full scalar/logarithmic factor is absorbed with one constant chosen
before every mesh, localization radius, and shading density. -/
theorem uniform_factor_absorption {D C G cNu a alpha eta eps : ℝ}
    (hP : 0 ≤ densityExponent D C) (hG : 1 ≤ G) (hcNu : 0 < cNu)
    (ha : 0 ≤ a) (halpha : 0 ≤ alpha)
    (hroom : eta+alpha*densityExponent D C < eps) :
    ∃ c : ℝ, 0 < c ∧ ∀ {m δ rho nu lam : ℝ},
      0 < δ → δ ≤ rho → rho ≤ 1 → 0 < nu → 0 < lam → nu ≤ G*rho →
      cNu*(Real.log (2/δ))^(-a)*rho^alpha*lam ≤ nu →
      c*δ^(m-D+eps)*lam^(densityExponent D C) ≤
        δ^(m-D+eta)*nu^C*rho^(D-C) := by
  let P := densityExponent D C
  let margin := eps-eta-alpha*P
  have hmargin : 0 < margin := by dsimp [margin,P]; linarith
  obtain ⟨ell,hell,hlog⟩ := PivotLossAbsorption.inverse_log_delta (mul_nonneg ha hP) hmargin
  let g := geometryCoefficient G D C
  have hg : 0 < g := geometryCoefficient_pos (zero_lt_one.trans_le hG)
  refine ⟨g*cNu^P*ell,by positivity,?_⟩
  intro m δ rho nu lam hδ hδrho hrho1 hnu hlam hupper hlower
  have hδ1 : δ ≤ 1 := hδrho.trans hrho1
  have hrho : 0 < rho := hδ.trans_le hδrho
  let L := Real.log (2/δ)
  have hL : 0 < L := Real.log_pos ((lt_div_iff₀ hδ).mpr (by linarith))
  have hlogs : ell*δ^margin ≤ L^(-(a*P)) := hlog δ hδ hδ1
  have hdensity : cNu^P*L^(-(a*P))*δ^(alpha*P)*lam^P ≤ nu^P :=
    density_lower hδ hδrho hlam hcNu hL halpha hP hlower
  have hcollapse : g*nu^P ≤ nu^C*rho^(D-C) := density_collapse hrho hrho1 hnu hG hupper
  have hδpow : δ^(m-D+eps) = δ^(m-D+eta)*δ^margin*δ^(alpha*P) := by
    rw [← Real.rpow_add hδ,← Real.rpow_add hδ]
    congr 1
    dsimp [margin]
    ring
  calc
    _ = δ^(m-D+eta)*g*(cNu^P*(ell*δ^margin)*δ^(alpha*P)*lam^P) := by
      rw [hδpow]
      ring
    _ ≤ δ^(m-D+eta)*g*(cNu^P*L^(-(a*P))*δ^(alpha*P)*lam^P) := by
      gcongr
    _ ≤ δ^(m-D+eta)*g*nu^P := mul_le_mul_of_nonneg_left hdensity (by positivity)
    _ = δ^(m-D+eta)*(g*nu^P) := by ring
    _ ≤ δ^(m-D+eta)*(nu^C*rho^(D-C)) := mul_le_mul_of_nonneg_left hcollapse (by positivity)
    _ = _ := by ring

/-- Preserve any nonnegative population/cap weight while applying the scalar
factor estimate to a genuine localized lower bound. -/
theorem uniform_localized_bound {D C G cNu cLocal a alpha eta eps : ℝ}
    (hP : 0 ≤ densityExponent D C) (hG : 1 ≤ G) (hcNu : 0 < cNu)
    (hcLocal : 0 < cLocal) (ha : 0 ≤ a) (halpha : 0 ≤ alpha)
    (hroom : eta+alpha*densityExponent D C < eps) :
    ∃ c : ℝ, 0 < c ∧ ∀ {m δ rho nu lam S E : ℝ},
      0 < δ → δ ≤ rho → rho ≤ 1 → 0 < nu → 0 < lam → 0 ≤ S →
      nu ≤ G*rho → cNu*(Real.log (2/δ))^(-a)*rho^alpha*lam ≤ nu →
      cLocal*δ^(m-D+eta)*nu^C*rho^(D-C)*S ≤ E →
      c*δ^(m-D+eps)*lam^(densityExponent D C)*S ≤ E := by
  obtain ⟨c,hc,hfactor⟩ := uniform_factor_absorption hP hG hcNu ha halpha hroom
  refine ⟨cLocal*c,mul_pos hcLocal hc,?_⟩
  intro m δ rho nu lam S E hδ hδrho hrho1 hnu hlam hS hupper hlower hlocal
  have hh := mul_le_mul_of_nonneg_right
    (mul_le_mul_of_nonneg_left (hfactor (m:=m) hδ hδrho hrho1 hnu hlam hupper hlower) hcLocal.le) hS
  apply le_trans ?_ hlocal
  simpa only [mul_assoc] using hh

/-- Proposition 8.1's scalar conclusion, with losses chosen before constants
that may themselves depend on the chosen two-ends exponent. Set exponent D
is unchanged; only the density exponent becomes max(D,C). -/
theorem uniform_globalization {D C eps : ℝ}
    (hD : 1 ≤ D) (hC : 1 ≤ C) (heps : 0 < eps) :
    ∃ alpha eta : ℝ, 0 < alpha ∧ alpha < 1 ∧ 0 < eta ∧
      ∀ {G cNu cLocal a : ℝ}, 1 ≤ G → 0 < cNu → 0 < cLocal → 0 ≤ a →
      ∃ c : ℝ, 0 < c ∧ ∀ {m δ rho nu lam M A E : ℝ},
      0 < δ → δ ≤ rho → rho ≤ 1 → 0 < nu → 0 < lam → 0 ≤ M → 0 < A →
      nu ≤ G*rho → cNu*(Real.log (2/δ))^(-a)*rho^alpha*lam ≤ nu →
      cLocal*A⁻¹*δ^(m-D+eta)*nu^C*rho^(D-C)*M ≤ E →
      c*A⁻¹*δ^(m-D+eps)*lam^(densityExponent D C)*M ≤ E := by
  obtain ⟨alpha,eta,halpha,halpha1,heta,hroom⟩ := choose_losses hD hC heps
  refine ⟨alpha,eta,halpha,halpha1,heta,?_⟩
  intro G cNu cLocal a hG hcNu hcLocal ha
  have hP : 0 ≤ densityExponent D C := (zero_le_one.trans hD).trans (le_max_left _ _)
  obtain ⟨c,hc,hbound⟩ := uniform_localized_bound hP hG hcNu hcLocal ha halpha.le hroom
  refine ⟨c,hc,?_⟩
  intro m δ rho nu lam M A E hδ hδrho hrho1 hnu hlam hM hA hupper hlower hlocal
  have hlocal' : cLocal*δ^(m-D+eta)*nu^C*rho^(D-C)*(A⁻¹*M) ≤ E := by
    convert hlocal using 1
    ring
  have hh := hbound hδ hδrho hrho1 hnu hlam (mul_nonneg (inv_pos.mpr hA).le hM) hupper hlower hlocal'
  convert hh using 1
  ring

end
end KakeyaFormal.TwoEndsGlobalizationAlgebra
