import UnrestrictedPivot

/-! Simultaneous weakening of diagonal set/density powers on actual grid
shadings. Positive integer shading counts supply delta≤2lambda, so the
loss is fixed; an arbitrary comparison of density powers alone would fail. -/
namespace KakeyaFormal
noncomputable section

/-- A stronger diagonal exponent implies each smaller diagonal exponent.
The actual nonempty-grid density lower bound pays only a fixed factor. -/
theorem DiagonalDiscreteEstimate.weaken {n : ℕ} {D d : ℝ}
    (h : DiagonalDiscreteEstimate n D) (hdD : d ≤ D) :
    DiagonalDiscreteEstimate n d := by
  intro geom eps heps
  obtain ⟨c,hc,hbound⟩ := h geom eps heps
  refine ⟨c/(2:ℝ)^(D-d),by positivity,?_⟩
  intro F
  by_cases hM : F.M=0
  · simp only [hM,Nat.cast_zero,mul_zero]
    exact Nat.cast_nonneg _
  have hδ := F.scale_pos
  have hlam := F.density_pos
  have hA : 0 < F.A := zero_lt_one.trans_le F.cap_ge_one
  have hratio : F.δ/F.lam ≤ 2 := by
    apply (div_le_iff₀ hlam).mpr
    have hh := F.density_ge_half_scale (Nat.pos_of_ne_zero hM)
    linarith
  have hpow := Real.rpow_le_rpow (div_pos hδ hlam).le hratio (sub_nonneg.mpr hdD)
  have hidentity : F.δ^((n:ℝ)-1-d+eps)*F.lam^d =
      F.δ^((n:ℝ)-1-D+eps)*F.lam^D*(F.δ/F.lam)^(D-d) := by
    rw [Real.div_rpow hδ.le hlam.le,Real.rpow_sub hlam]
    have hscale : F.δ^((n:ℝ)-1-d+eps) =
        F.δ^((n:ℝ)-1-D+eps)*F.δ^(D-d) := by
      rw [← Real.rpow_add hδ]
      congr 1
      ring
    rw [hscale]
    have hDp := (Real.rpow_pos_of_pos hlam D).ne'
    have hdp := (Real.rpow_pos_of_pos hlam d).ne'
    field_simp
  have hscaled := mul_le_mul_of_nonneg_left hpow
    (show 0 ≤ (c/(2:ℝ)^(D-d))*F.A⁻¹*
      (F.δ^((n:ℝ)-1-D+eps)*F.lam^D)*(F.M:ℝ) by positivity)
  have hnorm : (c/(2:ℝ)^(D-d))*F.A⁻¹*
      (F.δ^((n:ℝ)-1-D+eps)*F.lam^D)*(F.M:ℝ)*(2:ℝ)^(D-d) =
      c*F.A⁻¹*F.δ^((n:ℝ)-1-D+eps)*F.lam^D*(F.M:ℝ) := by
    have htwo := (Real.rpow_pos_of_pos (by norm_num : (0:ℝ)<2) (D-d)).ne'
    field_simp
  calc
    _ = (c/(2:ℝ)^(D-d))*F.A⁻¹*
        (F.δ^((n:ℝ)-1-D+eps)*F.lam^D)*(F.M:ℝ)*(F.δ/F.lam)^(D-d) := by
      calc
        _ = (c/(2:ℝ)^(D-d))*F.A⁻¹*(F.δ^((n:ℝ)-1-d+eps)*F.lam^d)*(F.M:ℝ) := by ring
        _ = _ := by rw [hidentity]; ring
    _ ≤ _ := hscaled
    _ = _ := hnorm
    _ ≤ _ := hbound F

namespace DiagonalConsequences

/-- The six-dimensional diagonal limit recorded in Section 9.1. -/
theorem six : DiagonalDiscreteEstimate 6 (29/7) := by
  apply DiagonalDiscreteEstimate.weaken (UnrestrictedPivot.diagonal_endpoint (n:=6) (by norm_num))
  have hh := KakeyaScalar.sqrt_two_rational_bounds.2
  norm_num [KakeyaScalar.limitProfile,KakeyaScalar.slopeLimit]
  linarith

/-- The eight-dimensional diagonal limit recorded in Section 9.1. -/
theorem eight : DiagonalDiscreteEstimate 8 (37/7) := by
  apply DiagonalDiscreteEstimate.weaken (UnrestrictedPivot.diagonal_endpoint (n:=8) (by norm_num))
  have hh := KakeyaScalar.sqrt_two_rational_bounds.2
  norm_num [KakeyaScalar.limitProfile,KakeyaScalar.slopeLimit]
  linarith

end DiagonalConsequences
end
end KakeyaFormal
