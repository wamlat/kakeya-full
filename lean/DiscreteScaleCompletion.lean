import CapCover
import CoarseBounds

/-! Complete any normalized discrete estimate above a fixed small-scale
cutoff using actual integer shadings and the finite projective cap cover.
This works for every real density exponent: on a nonempty family,
lambda >= delta/2 provides the needed fixed positive lower density. -/
namespace KakeyaFormal.DiscreteScaleCompletion
noncomputable section

def coefficient (k : ℕ) (m d p eps a : ℝ) : ℝ :=
  (ProjectiveGeometry.packingConstant k * max 1 (a^(-m)) *
    max 1 (a^(m-d+eps)) * max 1 ((a/2)^p))⁻¹

theorem coefficient_pos (k : ℕ) (m d p eps a : ℝ) :
    0 < coefficient k m d p eps a := by
  have hK : 0 < ProjectiveGeometry.packingConstant k :=
    zero_lt_one.trans_le (ProjectiveGeometry.packingConstant_ge_one k)
  have h₁ : 0 < max 1 (a^(-m)) := zero_lt_one.trans_le (le_max_left _ _)
  have h₂ : 0 < max 1 (a^(m-d+eps)) := zero_lt_one.trans_le (le_max_left _ _)
  have h₃ : 0 < max 1 ((a/2)^p) := zero_lt_one.trans_le (le_max_left _ _)
  exact inv_pos.mpr (by positivity)

/-- At a fixed lower mesh, the target is at most one occupied original cell.
Neither a separation nor a positive-exponent premise is needed here. -/
theorem bounded_scale {k : ℕ} {geom : Normalization} {m d p eps a : ℝ}
    (ha : 0 < a) (F : ShadedConfiguration (k+1) geom m) (hscale : a ≤ F.δ) :
    coefficient k m d p eps a * F.A⁻¹ * F.δ^(m-d+eps) * F.lam^p * F.M ≤
      (F.family.unionCells.card : ℝ) := by
  classical
  by_cases hM : F.M = 0
  · simp [hM]
  have hMpos : 0 < F.M := Nat.pos_of_ne_zero hM
  have hA : 0 < F.A := zero_lt_one.trans_le F.cap_ge_one
  have hpop := CapCover.cap_bound_total_count F.family F.scale_pos F.scale_le_one hA.le F.cap_bound
  rw [one_div,Real.inv_rpow F.scale_pos.le,← Real.rpow_neg F.scale_pos.le] at hpop
  have hcap := CoarseBounds.scale_power_upper ha hscale F.scale_le_one (e := -m)
  have hpow := CoarseBounds.scale_power_upper ha hscale F.scale_le_one (e := m-d+eps)
  have hlam := CoarseBounds.scale_power_upper (by positivity : 0 < a/2)
    ((div_le_div_of_nonneg_right hscale (by norm_num : (0:ℝ) ≤ 2)).trans
      (F.density_ge_half_scale hMpos)) F.density_le_one (e := p)
  let U := max 1 (a^(-m))
  let V := max 1 (a^(m-d+eps))
  let W := max 1 ((a/2)^p)
  let K := ProjectiveGeometry.packingConstant k
  have hK : 0 < K := zero_lt_one.trans_le (ProjectiveGeometry.packingConstant_ge_one k)
  have hU : 0 < U := zero_lt_one.trans_le (le_max_left _ _)
  have hV : 0 < V := zero_lt_one.trans_le (le_max_left _ _)
  have hW : 0 < W := zero_lt_one.trans_le (le_max_left _ _)
  have hpop' : (F.M:ℝ) ≤ K*F.A*U :=
    hpop.trans (mul_le_mul_of_nonneg_left hcap (by positivity))
  have hprod : F.δ^(m-d+eps)*F.lam^p*(F.M:ℝ) ≤ V*W*(K*F.A*U) := by
    exact mul_le_mul (mul_le_mul hpow hlam (Real.rpow_nonneg F.density_pos.le _) hV.le)
      hpop' (Nat.cast_nonneg _) (mul_nonneg hV.le hW.le)
  have hbound := mul_le_mul_of_nonneg_left hprod
    (mul_nonneg (coefficient_pos k m d p eps a).le (inv_pos.mpr hA).le)
  have hunit : coefficient k m d p eps a * F.A⁻¹ * (V*W*(K*F.A*U)) = 1 := by
    change (K*U*V*W)⁻¹ * F.A⁻¹ * (V*W*(K*F.A*U)) = 1
    field_simp
  have hnonempty : F.family.unionCells.Nonempty := by
    let i : Fin F.M := ⟨0,hMpos⟩
    have hpos : 0 < (F.family.shade i).card := by
      exact_mod_cast lt_of_lt_of_le (div_pos F.density_pos F.scale_pos) (F.comparable i).1
    obtain ⟨z,hz⟩ := Finset.card_pos.mp hpos
    exact ⟨z,F.family.shade_subset_union i hz⟩
  calc
    _ = (coefficient k m d p eps a * F.A⁻¹) *
        (F.δ^(m-d+eps)*F.lam^p*(F.M:ℝ)) := by ring
    _ ≤ (coefficient k m d p eps a * F.A⁻¹) * (V*W*(K*F.A*U)) := hbound
    _ = 1 := hunit
    _ ≤ (F.family.unionCells.card : ℝ) := by exact_mod_cast Finset.card_pos.mpr hnonempty

/-- Complete an estimate from any positive fixed cutoff. The small-scale
constant and cutoff are chosen before each actual configuration. -/
theorem complete {k : ℕ} {m d p : ℝ}
    (h : ∀ geom : Normalization, ∀ eps : ℝ, 0 < eps →
      ∃ a c : ℝ, 0 < a ∧ 0 < c ∧
        ∀ F : ShadedConfiguration (k+1) geom m, F.δ ≤ a →
          c*F.A⁻¹*F.δ^(m-d+eps)*F.lam^p*F.M ≤ (F.family.unionCells.card:ℝ)) :
    DiscreteEstimate (k+1) m d p := by
  intro geom eps heps
  obtain ⟨a,c,ha,hc,hsmall⟩ := h geom eps heps
  let C := coefficient k m d p eps a
  have hC : 0 < C := coefficient_pos k m d p eps a
  refine ⟨min c C,lt_min hc hC,?_⟩
  intro F
  have hfactor : 0 ≤ F.A⁻¹*F.δ^(m-d+eps)*F.lam^p*(F.M:ℝ) := by
    have hA := zero_lt_one.trans_le F.cap_ge_one
    have hd := F.scale_pos
    have hl := F.density_pos
    positivity
  by_cases hs : F.δ ≤ a
  · have hle := mul_le_mul_of_nonneg_right (min_le_left c C) hfactor
    apply le_trans ?_ (hsmall F hs)
    simpa only [mul_assoc] using hle
  · have hle := mul_le_mul_of_nonneg_right (min_le_right c C) hfactor
    apply le_trans ?_ (bounded_scale (d:=d) (p:=p) (eps:=eps) ha F (le_of_not_ge hs))
    simpa only [mul_assoc] using hle

end
end KakeyaFormal.DiscreteScaleCompletion
