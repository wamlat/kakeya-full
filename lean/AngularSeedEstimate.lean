import AngularSeedLogLoss

/-! A constructed finite two-ends hairbrush seed with a uniform epsilon loss.
The constant is chosen before the family, density, physical scale, and cap
constant. The original two-ends coefficient may have a fixed logarithmic cost. -/
namespace KakeyaFormal.AngularSeedEstimate
open AngularSeedPieces AngularSeedRealization AngularSeedBound AngularSeedHairbrush AngularSeedLogLoss
noncomputable section

/-- Replace the actual finite-depth constant by a single fixed logarithmic
budget. The estimate still concerns the original finite grid union. -/
theorem logarithmic_seed_with_pieces {k M : ℕ} (F : TubeFamily (k+2) M)
    {δ beta lam width alpha B B₀ b m A : ℝ} (P : Pieces F δ beta)
    (hδ : 0 < δ) (hlam : 0 < lam) (hlam1 : lam ≤ 1)
    (halpha : 0 < alpha) (hbeta : 0 < beta) (hbetaS : beta ≤ (m-1)/2)
    (hB : 1 ≤ B) (hB₀ : 1 ≤ B₀) (hm : 1 ≤ m) (hA : 1 ≤ A)
    (hBB : B ≤ B₀*(seedLog δ)^b)
    (hadm : F.Admissible width δ) (hcomp : F.Comparable δ lam)
    (hsep : F.Separated δ) (hcap : F.CapBound δ m A)
    (hends : ∀ i, ∀ x : Space (k+2), ∀ r : ℝ, δ ≤ r → r ≤ 1 →
      (((F.shade i).filter (fun z => dist (cellCenter δ z) x ≤ r)).card:ℝ) ≤
        B*r^alpha*((F.shade i).card:ℝ)) :
    uniformConstant k width alpha beta B₀ m/A*(seedLog δ)^(-uniformLoss k alpha beta b)*
      lam^2*(M:ℝ)*δ^((m-3)/2) ≤ (F.unionCells.card:ℝ) := by
  have hbase := finite_seed_at_depth F P hδ hlam hlam1 halpha hbeta hbetaS hB hm hA hadm hcomp hsep hcap hends
  have hpre := uniform_prefactor (width := width) P hδ halpha hbeta hB hB₀ hm hA hBB
  have hfac : 0 ≤ lam^2*(M:ℝ)*δ^(k+1)*δ^((m-1)/2) := by positivity
  have hvolume := (mul_le_mul_of_nonneg_right hpre hfac).trans (by
    convert hbase using 1 <;> first | rfl | ring)
  have hpow : δ^(k+2)*δ^((m-3)/2) = δ^(k+1)*δ^((m-1)/2) := by
    rw [← Real.rpow_natCast,← Real.rpow_natCast,← Real.rpow_add hδ,← Real.rpow_add hδ]
    congr 1
    push_cast
    ring
  apply (mul_le_mul_iff_right₀ (pow_pos hδ (k+2))).mp
  calc
    _ = (uniformConstant k width alpha beta B₀ m/A*(seedLog δ)^(-uniformLoss k alpha beta b))*
        (lam^2*(M:ℝ)*(δ^(k+2)*δ^((m-3)/2))) := by ring
    _ = _ := by rw [hpow]; ring
    _ ≤ _ := hvolume

/-- The chosen seed logarithm is no more than a fixed multiple of log(2/delta). -/
theorem seedLog_upper {δ : ℝ} (hδ : 0 < δ) (hδ1 : δ ≤ 1) :
    seedLog δ ≤ (3/Real.log 2)*Real.log (2/δ) := by
  have hlog2 : 0 < Real.log (2:ℝ) := Real.log_pos (by norm_num)
  have harg : (2:ℝ) ≤ 2/δ := (le_div_iff₀ hδ).mpr (by linarith)
  have hlog : Real.log (2:ℝ) ≤ Real.log (2/δ) := Real.log_le_log (by norm_num) harg
  unfold seedLog Real.logb
  apply (mul_le_mul_iff_right₀ hlog2).mp
  field_simp
  linarith

/-- Uniform absorption is proved for this actual logarithm, with no unstated
asymptotic dependence on the family or density. -/
theorem seedLog_absorption {P eps : ℝ} (hP : 0 ≤ P) (heps : 0 < eps) :
    ∃ c : ℝ, 0 < c ∧ ∀ δ : ℝ, 0 < δ → δ ≤ 1 → c*δ^eps ≤ (seedLog δ)^(-P) := by
  obtain ⟨ell,hell,hbound⟩ := inverse_log_power_uniform_bound hP heps
  have hC : 0 < (3:ℝ)/Real.log 2 := div_pos (by norm_num) (Real.log_pos (by norm_num))
  refine ⟨((3:ℝ)/Real.log 2)^(-P)*ell,mul_pos (Real.rpow_pos_of_pos hC _) hell,?_⟩
  intro δ hδ hδ1
  have hN : (1:ℝ) ≤ δ⁻¹ := by
    simpa only [one_div] using ((le_div_iff₀ hδ).mpr (by simpa using hδ1) : (1:ℝ) ≤ 1/δ)
  have hh := hbound δ⁻¹ hN
  rw [Real.inv_rpow hδ.le,Real.rpow_neg hδ.le,inv_inv] at hh
  simp only [← div_eq_mul_inv] at hh
  have hL : 0 < seedLog δ := zero_lt_one.trans_le (seedLog_ge_one hδ hδ1)
  have hlog : 0 < Real.log (2/δ) := Real.log_pos ((lt_div_iff₀ hδ).mpr (by linarith))
  have hsmall := Real.rpow_le_rpow_of_nonpos hL (seedLog_upper hδ hδ1) (neg_nonpos.mpr hP)
  rw [Real.mul_rpow hC.le hlog.le] at hsmall
  have hm := mul_le_mul_of_nonneg_left hh (Real.rpow_pos_of_pos hC (-P)).le
  exact (by ring : (((3:ℝ)/Real.log 2)^(-P)*ell)*δ^eps =
    ((3:ℝ)/Real.log 2)^(-P)*(ell*δ^eps)).trans_le (hm.trans hsmall)

/-- Actual finite two-ends seed for every original family. Constants depend
only on fixed exponents, physical width, and the prescribed logarithmic
budget, and never on delta, lambda, cap constant A, or tube population. -/
theorem two_ends_seed (k : ℕ) {width alpha beta B₀ b m eps : ℝ}
    (halpha : 0 < alpha) (hbeta : 0 < beta) (hbetaS : beta ≤ (m-1)/2)
    (hB₀ : 1 ≤ B₀) (hb : 0 ≤ b) (hm : 1 ≤ m) (heps : 0 < eps) :
    ∃ c : ℝ, 0 < c ∧ ∀ M : ℕ, ∀ F : TubeFamily (k+2) M, ∀ δ lam B A : ℝ,
      0 < δ → δ ≤ 1 → 0 < lam → lam ≤ 1 → 1 ≤ B → 1 ≤ A →
      B ≤ B₀*(seedLog δ)^b → F.Admissible width δ → F.Comparable δ lam →
      F.Separated δ → F.CapBound δ m A →
      (∀ i, ∀ x : Space (k+2), ∀ r : ℝ, δ ≤ r → r ≤ 1 →
        (((F.shade i).filter (fun z => dist (cellCenter δ z) x ≤ r)).card:ℝ) ≤
          B*r^alpha*((F.shade i).card:ℝ)) →
      c*A⁻¹*lam^2*(M:ℝ)*δ^((m-3)/2+eps) ≤ (F.unionCells.card:ℝ) := by
  obtain ⟨ell,hell,hlog⟩ := seedLog_absorption (uniformLoss_nonneg k halpha hbeta hb) heps
  have hC := uniformConstant_pos k width halpha hbeta hB₀ hm
  refine ⟨uniformConstant k width alpha beta B₀ m*ell,mul_pos hC hell,?_⟩
  intro M F δ lam B A hδ hδ1 hlam hlam1 hB hA hBB hadm hcomp hsep hcap hends
  by_cases hM : 0 < M
  · obtain ⟨P⟩ := exists_pieces F hM hδ hδ1 hbeta.le
    have hh := logarithmic_seed_with_pieces F P hδ hlam hlam1 halpha hbeta hbetaS
      hB hB₀ hm hA hBB hadm hcomp hsep hcap hends
    have hfac : 0 ≤ uniformConstant k width alpha beta B₀ m/A*lam^2*(M:ℝ)*δ^((m-3)/2) := by positivity
    have hmult := mul_le_mul_of_nonneg_left (hlog δ hδ hδ1) hfac
    calc
      _ = (uniformConstant k width alpha beta B₀ m/A*lam^2*(M:ℝ)*δ^((m-3)/2))*(ell*δ^eps) := by
        rw [Real.rpow_add hδ]
        simp only [div_eq_mul_inv]
        ring
      _ ≤ _ := hmult
      _ = uniformConstant k width alpha beta B₀ m/A*(seedLog δ)^(-uniformLoss k alpha beta b)*
          lam^2*(M:ℝ)*δ^((m-3)/2) := by ring
      _ ≤ _ := hh
  · have hz : M = 0 := by omega
    simp only [hz,Nat.cast_zero,mul_zero,zero_mul]
    exact Nat.cast_nonneg _

end
end KakeyaFormal.AngularSeedEstimate
