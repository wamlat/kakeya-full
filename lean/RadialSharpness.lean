import RadialPencil

/-! The actual radial pencil disproves a uniform unrestricted sublinear
cap coefficient. The counterexamples include both positive source errors, are
literal cumulative configurations, and use no supplied packing/count premise. -/
namespace KakeyaFormal.RadialSharpness
open RadialPencil ProjectiveGeometry
noncomputable section

theorem population_identity (k : ℕ) {N : ℕ} (hN : 0 < N) :
    (population k N:ℝ) = (1/RadialPencil.chartConstant k)^k*(scale k N)^(-(k:ℝ)) := by
  have hd : 0 < scale k N := scale_pos k hN
  rw [Real.rpow_neg hd.le,Real.rpow_natCast]
  apply (eq_mul_inv_iff_mul_eq₀ (ne_of_gt (pow_pos hd k))).mpr
  simpa only [mul_comm] using population_scale_identity k hN

/-- Exact evaluation of the source's putative sublinear-cap expression on
an actually constructed family; both epsilon losses remain visible. -/
theorem pencil_expression (k : ℕ) {N : ℕ} (hN : 0 < N) (m gamma eps c : ℝ) :
    c*(capCoefficient k N m)^(-gamma)*(scale k N)^((m-3)/2+eps)*
      (scale k N)^((m+3)/2+eps)*(population k N:ℝ) =
        (c*(fullDirectionCoefficient k 1)^(-gamma)*(1/RadialPencil.chartConstant k)^k)*
          (scale k N)^((m-(k:ℝ))*(1-gamma)+2*eps) := by
  have hd : 0 < scale k N := scale_pos k hN
  have hC : 0 < fullDirectionCoefficient k 1 :=
    zero_lt_one.trans_le (fullDirectionCoefficient_ge_one k (by norm_num))
  rw [population_identity k hN,capCoefficient,Real.mul_rpow hC.le (Real.rpow_nonneg hd.le _),
    ← Real.rpow_mul hd.le]
  have hexp : (m-(k:ℝ))*(1-gamma)+2*eps =
      (m-(k:ℝ))*(-gamma)+((m-3)/2+eps)+((m+3)/2+eps)+(-(k:ℝ)) := by ring
  rw [hexp]
  simp only [Real.rpow_add hd]
  ring

/-- Positive negative powers of the actual mesh become arbitrarily large
along the explicit pencil, with an arbitrary fixed positive prefactor. -/
theorem large_negative_power (k : ℕ) {c t : ℝ} (hc : 0 < c) (ht : 0 < t) :
    ∃ N : ℕ, 0 < N ∧ 1 < c*(scale k N)^(-t) := by
  have hcut : 0 < c^(1/t) := Real.rpow_pos_of_pos hc _
  obtain ⟨N,hN,hsmall⟩ := arbitrarily_small_scale k hcut
  have hp := Real.rpow_lt_rpow_of_neg (scale_pos k hN) hsmall (neg_neg_of_pos ht)
  have hid : (c^(1/t))^(-t) = c⁻¹ := by
    rw [← Real.rpow_mul hc.le,show (1/t)*(-t)=(-1:ℝ) by field_simp,Real.rpow_neg_one]
  rw [hid] at hp
  refine ⟨N,hN,?_⟩
  have hh := mul_lt_mul_of_pos_left hp hc
  simpa only [mul_inv_cancel₀ hc.ne'] using hh

/-- For every gamma<1, one fixed positive source error still leaves actual
radial counterexamples for every proposed positive uniform constant. -/
theorem counterexamples {k : ℕ} {m gamma : ℝ}
    (_hm1 : 1 < m) (hmk : m < (k:ℝ)) (hgamma : gamma < 1) :
    ∃ eps : ℝ, 0 < eps ∧ ∀ c : ℝ, 0 < c →
      ∃ F : CumulativeConfiguration (k+1) RadialPencil.geometry m,
        (F.family.unionCells.card:ℝ) <
          c*F.A^(-gamma)*F.δ^((m-3)/2+eps)*F.s^((m+3)/2+eps)*(F.M:ℝ) := by
  let gain := ((k:ℝ)-m)*(1-gamma)
  let eps := gain/4
  have hgain : 0 < gain := mul_pos (sub_pos.mpr hmk) (sub_pos.mpr hgamma)
  have heps : 0 < eps := by dsimp [eps]; positivity
  refine ⟨eps,heps,?_⟩
  intro c hc
  let prefactor := c*(fullDirectionCoefficient k 1)^(-gamma)*(1/RadialPencil.chartConstant k)^k
  have hchart : 0 < RadialPencil.chartConstant k :=
    lt_of_lt_of_le (by norm_num) (RadialPencil.chartConstant_ge_two k)
  have hpack : 0 < fullDirectionCoefficient k 1 :=
    zero_lt_one.trans_le (fullDirectionCoefficient_ge_one k (by norm_num))
  have hpref : 0 < prefactor := by dsimp [prefactor]; positivity
  have hhalf : 0 < gain/2 := by positivity
  obtain ⟨N,hN,hlarge⟩ := large_negative_power k hpref hhalf
  refine ⟨cumulativeConfiguration k hN hmk.le,?_⟩
  change ((family k N).unionCells.card:ℝ) <
    c*(capCoefficient k N m)^(-gamma)*(scale k N)^((m-3)/2+eps)*
      (scale k N)^((m+3)/2+eps)*(population k N:ℝ)
  rw [family_union_card k hN,pencil_expression k hN]
  have hexp : (m-(k:ℝ))*(1-gamma)+2*eps = -(gain/2) := by dsimp [eps,gain]; ring
  rw [hexp]
  exact hlarge

/-- Consequently no source-form unrestricted estimate can use A^(-gamma)
uniformly over actual cap coefficients when gamma<1. -/
theorem no_uniform_sublinear_cap {k : ℕ} {m gamma : ℝ}
    (hm1 : 1 < m) (hmk : m < (k:ℝ)) (hgamma : gamma < 1) :
    ¬ (∀ eps : ℝ, 0 < eps → ∃ c : ℝ, 0 < c ∧
      ∀ F : CumulativeConfiguration (k+1) RadialPencil.geometry m,
        c*F.A^(-gamma)*F.δ^((m-3)/2+eps)*F.s^((m+3)/2+eps)*(F.M:ℝ) ≤
          (F.family.unionCells.card:ℝ)) := by
  intro h
  obtain ⟨eps,heps,hcounter⟩ := counterexamples hm1 hmk hgamma
  obtain ⟨c,hc,hbound⟩ := h eps heps
  obtain ⟨F,hF⟩ := hcounter c hc
  exact (not_lt_of_ge (hbound F)) hF

/-- The very same construction already contradicts the proposed bound for
comparable shadings, not just for the larger cumulative class. -/
theorem comparable_counterexamples {k : ℕ} {m gamma : ℝ}
    (_hm1 : 1 < m) (hmk : m < (k:ℝ)) (hgamma : gamma < 1) :
    ∃ eps : ℝ, 0 < eps ∧ ∀ c : ℝ, 0 < c →
      ∃ F : ShadedConfiguration (k+1) RadialPencil.geometry m,
        (F.family.unionCells.card:ℝ) <
          c*F.A^(-gamma)*F.δ^((m-3)/2+eps)*F.lam^((m+3)/2+eps)*(F.M:ℝ) := by
  let gain := ((k:ℝ)-m)*(1-gamma)
  let eps := gain/4
  have hgain : 0 < gain := mul_pos (sub_pos.mpr hmk) (sub_pos.mpr hgamma)
  have heps : 0 < eps := by dsimp [eps]; positivity
  refine ⟨eps,heps,?_⟩
  intro c hc
  let prefactor := c*(fullDirectionCoefficient k 1)^(-gamma)*(1/RadialPencil.chartConstant k)^k
  have hchart : 0 < RadialPencil.chartConstant k :=
    lt_of_lt_of_le (by norm_num) (RadialPencil.chartConstant_ge_two k)
  have hpack : 0 < fullDirectionCoefficient k 1 :=
    zero_lt_one.trans_le (fullDirectionCoefficient_ge_one k (by norm_num))
  have hpref : 0 < prefactor := by dsimp [prefactor]; positivity
  have hhalf : 0 < gain/2 := by positivity
  obtain ⟨N,hN,hlarge⟩ := large_negative_power k hpref hhalf
  refine ⟨configuration k hN hmk.le,?_⟩
  change ((family k N).unionCells.card:ℝ) <
    c*(capCoefficient k N m)^(-gamma)*(scale k N)^((m-3)/2+eps)*
      (scale k N)^((m+3)/2+eps)*(population k N:ℝ)
  rw [family_union_card k hN,pencil_expression k hN]
  have hexp : (m-(k:ℝ))*(1-gamma)+2*eps = -(gain/2) := by dsimp [eps,gain]; ring
  rw [hexp]
  exact hlarge

theorem no_uniform_sublinear_cap_comparable {k : ℕ} {m gamma : ℝ}
    (hm1 : 1 < m) (hmk : m < (k:ℝ)) (hgamma : gamma < 1) :
    ¬ (∀ eps : ℝ, 0 < eps → ∃ c : ℝ, 0 < c ∧
      ∀ F : ShadedConfiguration (k+1) RadialPencil.geometry m,
        c*F.A^(-gamma)*F.δ^((m-3)/2+eps)*F.lam^((m+3)/2+eps)*(F.M:ℝ) ≤
          (F.family.unionCells.card:ℝ)) := by
  intro h
  obtain ⟨eps,heps,hcounter⟩ := comparable_counterexamples hm1 hmk hgamma
  obtain ⟨c,hc,hbound⟩ := h eps heps
  obtain ⟨F,hF⟩ := hcounter c hc
  exact (not_lt_of_ge (hbound F)) hF

end
end KakeyaFormal.RadialSharpness
