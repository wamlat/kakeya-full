import CapCover

/-! Actual coarse-scale bounds and extension of a uniform sufficiently-small-
scale estimate to all scales. Constants precede all concrete configurations. -/
namespace KakeyaFormal.CoarseBounds
open ProjectiveGeometry
noncomputable section

lemma scale_power_upper {δ a e : ℝ} (ha : 0 < a) (haδ : a ≤ δ) (hδ1 : δ ≤ 1) :
    δ^e ≤ max 1 (a^e) := by
  by_cases he : 0 ≤ e
  · exact (Real.rpow_le_one (ha.le.trans haδ) hδ1 he).trans (le_max_left _ _)
  · exact (Real.rpow_le_rpow_of_nonpos ha haδ (le_of_lt (lt_of_not_ge he))).trans (le_max_right _ _)

lemma coarse_scale_identity {δ m d eps : ℝ} (hδ : 0 < δ) :
    δ^(m-d+eps)*δ^(-m) = δ^(1-d+eps)/δ := by
  have heq : (1-d+eps)-1 = -d+eps := by ring
  have hh := Real.rpow_sub hδ (1-d+eps) 1
  rw [Real.rpow_one,heq] at hh
  rw [← hh,← Real.rpow_add hδ]
  congr 1
  ring

/-- One actual shading and the actual real-cap total-count bound control all
coarse configurations, for any target scale exponent and density power≥1. -/
theorem coarse_configuration_bound {k : ℕ} {m d p eps a : ℝ} (ha : 0 < a) (hp : 1 ≤ p)
    (geom : Normalization) (F : ShadedConfiguration (k+1) geom m) (hscale : a ≤ F.δ) :
    (1/(packingConstant k*max 1 (a^(1-d+eps))))*F.A⁻¹*F.δ^(m-d+eps)*F.lam^p*F.M ≤
      (F.family.unionCells.card:ℝ) := by
  classical
  by_cases hM : F.M = 0
  · simp only [hM,Nat.cast_zero,mul_zero]
    positivity
  have hMpos : 0 < F.M := Nat.pos_of_ne_zero hM
  let i : Fin F.M := ⟨0,hMpos⟩
  have hsubset : F.family.shade i ⊆ F.family.unionCells := by
    intro z hz
    exact Finset.mem_biUnion.mpr ⟨i,Finset.mem_univ _,hz⟩
  have hunion : F.lam/F.δ ≤ (F.family.unionCells.card:ℝ) :=
    (F.comparable i).1.trans (by exact_mod_cast Finset.card_le_card hsubset)
  have hA : 0 < F.A := zero_lt_one.trans_le F.cap_ge_one
  have hP : 0 < packingConstant k := zero_lt_one.trans_le (packingConstant_ge_one k)
  let H := max 1 (a^(1-d+eps))
  have hH : 0 < H := zero_lt_one.trans_le (le_max_left _ _)
  have hcount := CapCover.cap_bound_total_count_scale F.family F.scale_pos F.scale_le_one hA.le F.cap_bound
  have hmul := mul_le_mul_of_nonneg_left hcount
    (by positivity [F.scale_pos,F.density_pos] : 0 ≤ F.A⁻¹*F.δ^(m-d+eps)*F.lam^p)
  have hid : (F.A⁻¹*F.δ^(m-d+eps)*F.lam^p)*(packingConstant k*F.A*F.δ^(-m)) =
      packingConstant k*F.δ^(1-d+eps)*F.lam^p/F.δ := by
    calc
      _ = packingConstant k*(F.δ^(m-d+eps)*F.δ^(-m))*F.lam^p := by field_simp
      _ = _ := by rw [coarse_scale_identity F.scale_pos]; ring
  rw [hid] at hmul
  have hlam : F.lam^p ≤ F.lam := by
    simpa only [Real.rpow_one] using Real.rpow_le_rpow_of_exponent_ge F.density_pos F.density_le_one hp
  have hpow : F.δ^(1-d+eps) ≤ H := scale_power_upper ha hscale F.scale_le_one
  have hboth := mul_le_mul hpow hlam (Real.rpow_nonneg F.density_pos.le p) hH.le
  have hh := div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_left hboth hP.le) F.scale_pos.le
  have htarget := mul_le_mul_of_nonneg_left hunion (mul_pos hP hH).le
  have hbound : F.A⁻¹*F.δ^(m-d+eps)*F.lam^p*F.M ≤
      (packingConstant k*H)*(F.family.unionCells.card:ℝ) := by
    have hmid : packingConstant k*F.δ^(1-d+eps)*F.lam^p/F.δ ≤
        (packingConstant k*H)*(F.lam/F.δ) := by
      simpa only [mul_assoc,mul_div_assoc] using hh
    exact hmul.trans (hmid.trans htarget)
  have hdiv : (F.A⁻¹*F.δ^(m-d+eps)*F.lam^p*F.M)/(packingConstant k*H) ≤
      (F.family.unionCells.card:ℝ) := by
    apply (div_le_iff₀ (mul_pos hP hH)).mpr
    simpa only [mul_assoc,mul_comm,mul_left_comm] using hbound
  simpa only [one_div,div_eq_mul_inv,mul_assoc,mul_comm,mul_left_comm,one_mul,mul_one] using hdiv

end
end KakeyaFormal.CoarseBounds

namespace KakeyaFormal
open CoarseBounds ProjectiveGeometry
noncomputable section

/-- It suffices to establish the concrete estimate below a positive threshold
chosen before each configuration; all remaining scales are handled internally. -/
theorem DiscreteEstimate.of_small_scales {k : ℕ} {m d p : ℝ} (hp : 1 ≤ p)
    (hsmall : ∀ geom : Normalization, ∀ eps : ℝ, 0 < eps →
      ∃ a c : ℝ, 0 < a ∧ 0 < c ∧ ∀ F : ShadedConfiguration (k+1) geom m, F.δ ≤ a →
        c*F.A⁻¹*F.δ^(m-d+eps)*F.lam^p*F.M ≤ (F.family.unionCells.card:ℝ)) :
    DiscreteEstimate (k+1) m d p := by
  intro geom eps heps
  obtain ⟨a,c,ha,hc,hfine⟩ := hsmall geom eps heps
  let C := 1/(packingConstant k*max 1 (a^(1-d+eps)))
  have hP : 0 < packingConstant k := zero_lt_one.trans_le (packingConstant_ge_one k)
  have hC : 0 < C := by dsimp [C]; positivity
  refine ⟨min c C,lt_min hc hC,?_⟩
  intro F
  have hcoef : 0 ≤ F.A⁻¹*F.δ^(m-d+eps)*F.lam^p*F.M := by
    have hA : 0 < F.A := zero_lt_one.trans_le F.cap_ge_one
    positivity [F.scale_pos,F.density_pos]
  by_cases hfineScale : F.δ ≤ a
  · have hh := mul_le_mul_of_nonneg_right (min_le_left c C) hcoef
    have hh' : (min c C)*F.A⁻¹*F.δ^(m-d+eps)*F.lam^p*F.M ≤
        c*F.A⁻¹*F.δ^(m-d+eps)*F.lam^p*F.M := by simpa only [mul_assoc] using hh
    exact hh'.trans (hfine F hfineScale)
  · have hh := mul_le_mul_of_nonneg_right (min_le_right c C) hcoef
    have hh' : (min c C)*F.A⁻¹*F.δ^(m-d+eps)*F.lam^p*F.M ≤
        C*F.A⁻¹*F.δ^(m-d+eps)*F.lam^p*F.M := by simpa only [mul_assoc] using hh
    exact hh'.trans
      (coarse_configuration_bound ha hp geom F (le_of_lt (lt_of_not_ge hfineScale)))

end
end KakeyaFormal
