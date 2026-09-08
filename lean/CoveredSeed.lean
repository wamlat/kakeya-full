import SeedGlobalizationAlgebra

/-! Globalization of the actual two-ends seed for a family whose full
shadings fit unit balls. Common radius and density classes are constructed. -/
namespace KakeyaFormal.CoveredSeed
open FiniteGridLocalization FiniteLocalizedFamily LocalizedSeedNormalization
open LocalizedSeedApplication SeedGlobalizationAlgebra AngularSeedLogLoss
noncomputable section
open Classical

theorem countConstant_pos (k : ℕ) (width : ℝ) : 0 < countConstant k width := by
  have hW := LocalizedGridTubes.localWidth_pos width
  unfold countConstant
  positivity

/-- The actual unrestricted family obeys the globalized seed, with only the
explicit small localization exponent error and two class logarithms. -/
theorem covered_seed (k : ℕ) {width alpha beta m eps : ℝ}
    (halpha : 0 < alpha) (halpha1 : alpha < 1) (hbeta : 0 < beta)
    (hbetaS : beta ≤ (m-1)/2) (hm : 1 ≤ m) (heps : 0 < eps) :
    ∃ c : ℝ, 0 < c ∧ ∀ M : ℕ, ∀ F : TubeFamily (k+2) M, ∀ δ lam A : ℝ,
      0 < M → 0 < δ → δ ≤ 1 → 0 < lam → 1 ≤ A →
      F.Admissible width δ → F.Comparable δ lam → F.CapBound δ m A →
      ∀ centers : Fin M → Space (k+2),
      (∀ i z, z ∈ F.shade i → dist (cellCenter δ z) (centers i) ≤ 1) →
      c*A⁻¹*δ^((m-3)/2+eps)*lam^(densityPower ((m+3)/2) alpha)*
        (seedLog δ)^(-(2:ℝ))*(M:ℝ) ≤ (F.unionCells.card:ℝ) := by
  obtain ⟨c,hc,hlocal⟩ := localized_seed k (width := width) halpha hbeta hbetaS hm heps
  let C := countConstant (k+2) width
  let d := (m+3)/2
  let q := radiusPower d alpha
  have hC : 0 < C := countConstant_pos _ _
  have hd : 2 ≤ d := by dsimp [d]; linarith
  refine ⟨c*C^(-q)/(alpha+3),by positivity,?_⟩
  intro M F δ lam A hM hδ hδ1 hlam hA hadm hcomp hcap centers hcover
  obtain ⟨S⟩ := FiniteGridLocalization.exists_selection F hM hδ hδ1 halpha.le hlam hcomp centers hcover
  have hN : 0 < S.selected.card := Finset.card_pos.mpr S.nonempty
  have hrho : 0 < S.rho := hδ.trans_le S.radius_lower
  have hloc := hlocal S.selected.card (FiniteLocalizedFamily.family S) δ S.rho S.s A
    hN hδ S.radius_lower S.radius_upper S.density_pos hA
    (family_admissible S hadm) (family_comparable S) (family_cap_bound S hcap)
    (fun i => S.centers (FiniteLocalizedFamily.index S i)) (family_ball S) (family_two_ends S)
  have hU : (((FiniteLocalizedFamily.family S).unionCells.card):ℝ) ≤ (F.unionCells.card:ℝ) :=
    Nat.cast_le.mpr (Finset.card_le_card (family_union_subset S))
  have hden := localized_density_lower hlam hC hrho hd halpha.le halpha1
    (radius_density S hδ hadm) S.density_lower
  have hcount := selected_count_log S hδ halpha.le
  have hL : 0 < seedLog δ := zero_lt_one.trans_le (seedLog_ge_one hδ hδ1)
  have hprod := mul_le_mul hden hcount (by positivity : (0:ℝ) ≤ (M:ℝ)/((alpha+3)*(seedLog δ)^2))
    (by positivity : (0:ℝ) ≤ S.s^2*S.rho^(d-2))
  have hfac : 0 ≤ c*A⁻¹*δ^((m-3)/2+eps) := by positivity
  have hscaled := mul_le_mul_of_nonneg_left hprod hfac
  have hexp : d-2 = (m-1)/2 := by dsimp [d]; ring
  calc
    _ = (c*A⁻¹*δ^((m-3)/2+eps))*
        ((C^(-q)*lam^(densityPower d alpha))*((M:ℝ)/((alpha+3)*(seedLog δ)^2))) := by
      dsimp only [d]
      rw [Real.rpow_neg hL.le,Real.rpow_two]
      simp only [div_eq_mul_inv,mul_inv_rev]
      ring
    _ ≤ _ := hscaled
    _ = c*A⁻¹*δ^((m-3)/2+eps)*S.s^2*S.rho^((m-1)/2)*(S.selected.card:ℝ) := by
      rw [hexp]
      ring
    _ ≤ _ := hloc.trans hU

end
end KakeyaFormal.CoveredSeed
