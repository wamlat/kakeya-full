import PivotLossAbsorption

/-! The deterministic low-cell branch of Section 7. Positive scale margin
absorbs its marked-fraction and cutoff logarithms uniformly at every scale.
No random realization, lower density cutoff, or desired pivot estimate is an
input. The last results transport original-scale logarithmic budgets into the
complement of the coarse-eccentricity case. -/
namespace KakeyaFormal.LowCellAbsorption
noncomputable section

/-- Exact normalization of the literal sampling low branch. This identity is
valid even when a scalar is zero; applications separately prove positivity. -/
theorem threshold_low_identity (R H xi lam M δ L : ℝ) :
    ((1/R)*(xi*lam*M/δ))/(2*(H*L)) =
      (1/(2*R*H))*xi*lam*M/(δ*L) := by
  simp only [div_eq_mul_inv,mul_inv_rev,one_mul]
  ring

/-- In the complementary coarse range, the original logarithm is bounded by
a fixed multiple of the normalized logarithm, including the additive log 2. -/
theorem log_eccentricity_transport {N N' a : ℝ}
    (hN : 0 < N) (hN' : 0 < N') (ha : 1 ≤ a)
    (hcutoff : N^(1/a) ≤ N') :
    Real.log (2*N) ≤ a*Real.log (2*N') := by
  have ha0 : 0 < a := by linarith
  have hh := Real.rpow_le_rpow (Real.rpow_nonneg hN.le (1/a)) hcutoff ha0.le
  rw [← Real.rpow_mul hN.le,one_div_mul_cancel ha0.ne',Real.rpow_one] at hh
  have hlogs := Real.log_le_log hN hh
  rw [Real.log_rpow hN'] at hlogs
  rw [Real.log_mul (by norm_num : (2:ℝ) ≠ 0) hN.ne',
    Real.log_mul (by norm_num : (2:ℝ) ≠ 0) hN'.ne']
  have htwo := mul_le_mul_of_nonneg_right ha
    (Real.log_nonneg (by norm_num : (1:ℝ) ≤ 2))
  nlinarith

/-- The source logarithm is comparable to the normalized logarithm whenever
the normalized mesh to a fixed power is at most the original mesh. -/
theorem log_scale_transport {δ δ' a : ℝ}
    (hδ : 0 < δ) (hδ' : 0 < δ') (ha : 1 ≤ a)
    (hscale : δ'^a ≤ δ) :
    Real.log (2/δ) ≤ a*Real.log (2/δ') := by
  have hh := Real.log_le_log (Real.rpow_pos_of_pos hδ' a) hscale
  rw [Real.log_rpow hδ'] at hh
  rw [Real.log_div (by norm_num : (2:ℝ) ≠ 0) hδ.ne',
    Real.log_div (by norm_num : (2:ℝ) ≠ 0) hδ'.ne']
  have htwo := mul_le_mul_of_nonneg_right ha (Real.log_nonneg (by norm_num : (1:ℝ) ≤ 2))
  nlinarith

/-- This is the complementary source cutoff `N' ≥ N^(1/a)` in mesh variables. -/
theorem log_scale_transport_of_power_cutoff {δ δ' a : ℝ}
    (hδ : 0 < δ) (hδ' : 0 < δ') (ha : 1 ≤ a)
    (hscale : δ' ≤ δ^(1/a)) :
    Real.log (2/δ) ≤ a*Real.log (2/δ') := by
  have ha0 : 0 < a := by linarith
  apply log_scale_transport hδ hδ' ha
  have hh := Real.rpow_le_rpow hδ'.le hscale ha0.le
  rw [← Real.rpow_mul hδ.le,one_div_mul_cancel ha0.ne',Real.rpow_one] at hh
  exact hh

/-- A marked-fraction budget expressed at the original scale transfers with
only the fixed factor `a^(-x)`. -/
theorem inverse_log_scale_transport {δ δ' a xi xi₀ x : ℝ}
    (hδ : 0 < δ) (hδ1 : δ ≤ 1) (hδ' : 0 < δ') (hδ'1 : δ' ≤ 1)
    (ha : 1 ≤ a) (hxi₀ : 0 < xi₀) (hx : 0 ≤ x)
    (hscale : δ'^a ≤ δ) (hxi : xi₀*(Real.log (2/δ))^(-x) ≤ xi) :
    (xi₀*a^(-x))*(Real.log (2/δ'))^(-x) ≤ xi := by
  have hL : 0 < Real.log (2/δ) :=
    Real.log_pos ((lt_div_iff₀ hδ).mpr (by linarith))
  have hL' : 0 < Real.log (2/δ') :=
    Real.log_pos ((lt_div_iff₀ hδ').mpr (by linarith))
  have ha0 : 0 < a := by linarith
  have hh := Real.rpow_le_rpow_of_nonpos hL (log_scale_transport hδ hδ' ha hscale)
    (by linarith : -x ≤ 0)
  rw [Real.mul_rpow ha0.le hL'.le] at hh
  have hmul := mul_le_mul_of_nonneg_left hh hxi₀.le
  have hfirst : (xi₀*a^(-x))*(Real.log (2/δ'))^(-x) ≤
      xi₀*(Real.log (2/δ))^(-x) := by simpa only [mul_assoc] using hmul
  exact hfirst.trans hxi

/-- Uniform absorption of the actual low-cell count. The constant precedes
all scales, densities, marked fractions, populations, and support counts.
The positive margin permits even zero final scale loss. -/
theorem uniform_low_bound {cLow xi₀ x C m D eps : ℝ}
    (hcLow : 0 < cLow) (hxi₀ : 0 < xi₀) (hx : 0 ≤ x) (hC : 1 ≤ C)
    (hD : D < m+1) (heps : 0 ≤ eps) :
    ∃ c : ℝ, 0 < c ∧ ∀ {δ lam xi M E : ℝ},
      0 < δ → δ ≤ 1 → 0 < lam → lam ≤ 1 → 0 ≤ M →
      xi₀*(Real.log (2/δ))^(-x) ≤ xi →
      cLow*xi*lam*M/(δ*Real.log (2/δ)) ≤ E →
      c*δ^(m-D+eps)*lam^C*M ≤ E := by
  let margin := m+1-D+eps
  have hmargin : 0 < margin := by dsimp [margin]; linarith
  obtain ⟨ell,hell,hlog⟩ := PivotLossAbsorption.inverse_log_delta
    (by linarith : 0 ≤ x+1) hmargin
  refine ⟨cLow*xi₀*ell,by positivity,?_⟩
  intro δ lam xi M E hδ hδ1 hlam hlam1 hM hxi hlow
  let L := Real.log (2/δ)
  have hL : 0 < L := Real.log_pos ((lt_div_iff₀ hδ).mpr (by linarith))
  have hxi0 : 0 < xi := (by positivity : 0 < xi₀*L^(-x)).trans_le hxi
  have hpow : lam^C ≤ lam := by
    simpa only [Real.rpow_one] using
      Real.rpow_le_rpow_of_exponent_ge hlam hlam1 hC
  have hlogs : ell*δ^margin ≤ L^(-(x+1)) := hlog δ hδ hδ1
  have hxiDiv : (xi₀*L^(-x))/L ≤ xi/L :=
    div_le_div_of_nonneg_right hxi hL.le
  have hδpow : δ^margin = δ^(m-D+eps)*δ := by
    rw [show margin = (m-D+eps)+1 by dsimp [margin]; ring,
      Real.rpow_add hδ,Real.rpow_one]
  have hLpow : L^(-(x+1)) = L^(-x)/L := by
    rw [show -(x+1) = -x-1 by ring,Real.rpow_sub hL,Real.rpow_one]
  calc
    (cLow*xi₀*ell)*δ^(m-D+eps)*lam^C*M =
        (cLow*xi₀*lam^C*M/δ)*(ell*δ^margin) := by rw [hδpow]; field_simp
    _ ≤ (cLow*xi₀*lam^C*M/δ)*L^(-(x+1)) :=
      mul_le_mul_of_nonneg_left hlogs (by positivity)
    _ = (cLow*lam^C*M/δ)*((xi₀*L^(-x))/L) := by rw [hLpow]; ring
    _ ≤ (cLow*lam^C*M/δ)*(xi/L) :=
      mul_le_mul_of_nonneg_left hxiDiv (by positivity)
    _ = (cLow*xi*M/(δ*L))*lam^C := by ring
    _ ≤ (cLow*xi*M/(δ*L))*lam := mul_le_mul_of_nonneg_left hpow (by positivity)
    _ = cLow*xi*lam*M/(δ*L) := by ring
    _ ≤ E := hlow

/-- The same deterministic branch also supplies the conventional inverse-cap
factor uniformly for every `A≥1`. -/
theorem uniform_low_cap_bound {cLow xi₀ x C m D eps : ℝ}
    (hcLow : 0 < cLow) (hxi₀ : 0 < xi₀) (hx : 0 ≤ x) (hC : 1 ≤ C)
    (hD : D < m+1) (heps : 0 ≤ eps) :
    ∃ c : ℝ, 0 < c ∧ ∀ {δ lam xi M E A : ℝ},
      0 < δ → δ ≤ 1 → 0 < lam → lam ≤ 1 → 0 ≤ M → 1 ≤ A →
      xi₀*(Real.log (2/δ))^(-x) ≤ xi →
      cLow*xi*lam*M/(δ*Real.log (2/δ)) ≤ E →
      c*A⁻¹*δ^(m-D+eps)*lam^C*M ≤ E := by
  obtain ⟨c,hc,hbound⟩ := uniform_low_bound hcLow hxi₀ hx hC hD heps
  refine ⟨c,hc,?_⟩
  intro δ lam xi M E A hδ hδ1 hlam hlam1 hM hA hxi hlow
  have hinv : A⁻¹ ≤ 1 := inv_le_one_of_one_le₀ hA
  have hh := mul_le_mul_of_nonneg_right hinv
    (by positivity : 0 ≤ c*δ^(m-D+eps)*lam^C*M)
  have hmain := hbound hδ hδ1 hlam hlam1 hM hxi hlow
  calc
    _ = A⁻¹*(c*δ^(m-D+eps)*lam^C*M) := by ring
    _ ≤ 1*(c*δ^(m-D+eps)*lam^C*M) := hh
    _ ≤ E := by simpa only [one_mul] using hmain

/-- Original logarithmic marked budgets suffice in the complement of the
coarse case. Only a fixed constant changes under logarithmic transport. -/
theorem uniform_original_log_low_bound {cLow xi₀ x C m D eps a : ℝ}
    (hcLow : 0 < cLow) (hxi₀ : 0 < xi₀) (hx : 0 ≤ x) (hC : 1 ≤ C)
    (hD : D < m+1) (heps : 0 ≤ eps) (ha : 1 ≤ a) :
    ∃ c : ℝ, 0 < c ∧ ∀ {δ δ' lam xi M E : ℝ},
      0 < δ → δ ≤ 1 → 0 < δ' → δ' ≤ 1 → δ'^a ≤ δ →
      0 < lam → lam ≤ 1 → 0 ≤ M →
      xi₀*(Real.log (2/δ))^(-x) ≤ xi →
      cLow*xi*lam*M/(δ'*Real.log (2/δ')) ≤ E →
      c*δ'^(m-D+eps)*lam^C*M ≤ E := by
  have ha0 : 0 < a := by linarith
  obtain ⟨c,hc,hbound⟩ := uniform_low_bound hcLow
    (by positivity : 0 < xi₀*a^(-x)) hx hC hD heps
  refine ⟨c,hc,?_⟩
  intro δ δ' lam xi M E hδ hδ1 hδ' hδ'1 hscale hlam hlam1 hM hxi hlow
  exact hbound hδ' hδ'1 hlam hlam1 hM
    (inverse_log_scale_transport hδ hδ1 hδ' hδ'1 ha hxi₀ hx hscale hxi) hlow

end
end KakeyaFormal.LowCellAbsorption
