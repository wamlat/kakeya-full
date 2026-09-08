import TwoEndsGlobalization
import LogarithmicTwoEndsAlgebra

/-! Uniform estimates for an ORIGINAL logarithmically growing two-ends
coefficient. Actual localization at half the original exponent cannot choose
a smaller-than-polylogarithmic radius, so it preserves the density exponent.
No varying coefficient is passed to the fixed-coefficient analytic theorem. -/
namespace KakeyaFormal.LogarithmicTwoEnds
open Finset FiniteGridLocalization FiniteLocalizedFamily TwoEndsGlobalization
noncomputable section
open Classical

/-- The original two-ends inequality bounds the radius of the actual selected
localization. The factor two comes from original comparable row cardinalities;
no unrecorded original-row mass-retention property is assumed. -/
theorem radius_constraint {n M : ℕ} (F : TubeFamily n M) {δ beta lam B : ℝ}
    (S : Selection F δ beta lam) (hδ : 0 < δ) (hlam : 0 < lam) (hB : 0 ≤ B)
    (hcomp : F.Comparable δ lam) (hends : F.FullTwoEnds δ B (2*beta)) :
    1 ≤ 2*B*S.rho^beta := by
  obtain ⟨i,hi⟩ := S.nonempty
  have hrho : 0 < S.rho := hδ.trans_le S.radius_lower
  have hcount := hends i (S.centers i) S.rho S.radius_lower S.radius_upper
  have hupper := mul_le_mul_of_nonneg_left (hcomp i).2
    (mul_nonneg hB (Real.rpow_nonneg hrho.le (2*beta)))
  have hslocal : S.s/δ ≤ B*S.rho^(2*beta)*(2*lam/δ) :=
    (S.comparable i hi).1.trans (hcount.trans hupper)
  have hs : S.s ≤ 2*B*S.rho^(2*beta)*lam := by
    have hid : B*S.rho^(2*beta)*(2*lam/δ) = (2*B*S.rho^(2*beta)*lam)/δ := by ring
    rw [hid] at hslocal
    exact (div_le_div_iff_of_pos_right hδ).mp hslocal
  have hcancel : S.rho^beta ≤ 2*B*S.rho^(2*beta) :=
    (mul_le_mul_iff_left₀ hlam).mp (S.density_lower.trans hs)
  have hpow : S.rho^(2*beta) = S.rho^beta*S.rho^beta := by
    rw [← Real.rpow_add hrho]
    congr 1
    ring
  apply (mul_le_mul_iff_left₀ (Real.rpow_pos_of_pos hrho beta)).mp
  calc
    1*S.rho^beta = S.rho^beta := one_mul _
    _ ≤ 2*B*S.rho^(2*beta) := hcancel
    _ = (2*B*S.rho^beta)*S.rho^beta := by rw [hpow]; ring

/-- A fixed-coefficient two-ends estimate implies the SAME density exponent
for original coefficients bounded by an arbitrary fixed power of log(2/delta).
All constants, including the local analytic input coefficient, precede the
actual configuration and its original varying ball coefficient. -/
theorem estimate {k : ℕ} {m D C : ℝ}
    (hestimate : TwoEndsDiscreteEstimate (k+1) m D C) (hm : 0 ≤ m) (hC : 1 ≤ C)
    (geom : Normalization) (B₀ alpha b eps : ℝ)
    (hB₀ : 1 ≤ B₀) (ha : 0 < alpha) (hb : 0 ≤ b) (heps : 0 < eps) :
    ∃ c : ℝ, 0 < c ∧ ∀ F : ShadedConfiguration (k+1) geom m,
      F.family.FullTwoEnds F.δ (B₀*(Real.log (2/F.δ))^b) alpha →
      c*F.A⁻¹*F.δ^(m-D+eps)*F.lam^C*F.M ≤ (F.family.unionCells.card:ℝ) := by
  let beta := alpha/2
  have hbeta : 0 < beta := by dsimp [beta]; positivity
  have hbetaEq : 2*beta = alpha := by dsimp [beta]; ring
  let P := max 0 (beta*C+D-C)
  let q := P/beta
  have hP : 0 ≤ P := le_max_left _ _
  have hq : 0 ≤ q := div_nonneg hP hbeta.le
  have hB₀p : 0 < B₀ := zero_lt_one.trans_le hB₀
  let a := (2*B₀)^(-q)
  have haPos : 0 < a := Real.rpow_pos_of_pos (by positivity) _
  have hBlocal : (1:ℝ) ≤ (4:ℝ)^beta := Real.one_le_rpow (by norm_num) hbeta.le
  obtain ⟨cLocal,hcLocal,hlocal⟩ := LocalizedTwoEndsApplication.localized_bound k
    (width:=geom.width) hestimate hbeta hBlocal hm (zero_le_one.trans hC)
    (show 0 < eps/2 by positivity)
  obtain ⟨ell,hell,hlog⟩ := PivotLossAbsorption.inverse_log_delta
    (show 0 ≤ b*q+2 by positivity) (show 0 < eps/2 by positivity)
  have hpop := populationCoefficient_pos hbeta.le
  let cFine := cLocal*a*populationCoefficient beta*ell
  have hcFine : 0 < cFine := by dsimp [cFine]; positivity
  let cutoff := 1/(2*geom.width)
  have hcutoff : 0 < cutoff := by dsimp [cutoff]; positivity [geom.width_pos]
  have hfine (F : ShadedConfiguration (k+1) geom m) (hsmall : F.δ ≤ cutoff)
      (hends : F.family.FullTwoEnds F.δ (B₀*(Real.log (2/F.δ))^b) alpha) :
      cFine*F.A⁻¹*F.δ^(m-D+eps)*F.lam^C*F.M ≤ (F.family.unionCells.card:ℝ) := by
    by_cases hM : F.M = 0
    · simp [hM]
    have hMp : 0 < F.M := Nat.pos_of_ne_zero hM
    have hδ := F.scale_pos
    have hAp : 0 < F.A := zero_lt_one.trans_le F.cap_ge_one
    let L := Real.log (2/F.δ)
    have hL : 0 < L := Real.log_pos
      ((lt_div_iff₀ hδ).mpr (by linarith [F.scale_le_one]))
    have hwidth : geom.width*F.δ ≤ (1:ℝ)/2 := by
      have hh := mul_le_mul_of_nonneg_left hsmall geom.width_pos.le
      have hid : geom.width*cutoff = (1:ℝ)/2 := by dsimp [cutoff]; field_simp [ne_of_gt geom.width_pos]
      exact hh.trans_eq hid
    obtain ⟨S⟩ := FiniteGridLocalization.exists_selection F.family hMp hδ F.scale_le_one
      hbeta.le F.density_pos F.comparable (fun i => (F.family.tube i).axisPoint (1/2))
      (unit_ball_cover F.family F.admissible hwidth)
    have hrho : 0 < S.rho := hδ.trans_le S.radius_lower
    have hselected : 0 < S.selected.card := Finset.card_pos.mpr S.nonempty
    have hendsBeta : F.family.FullTwoEnds F.δ (B₀*L^b) (2*beta) := by
      rw [hbetaEq]
      exact hends
    have hradius := radius_constraint F.family S hδ F.density_pos
      (by positivity : 0 ≤ B₀*L^b) F.comparable hendsBeta
    have hnum : a*L^(-(b*q))*F.lam^C ≤ S.s^C*S.rho^(D-C) := by
      exact LogarithmicTwoEndsAlgebra.density_factor hbeta (zero_le_one.trans hC)
        hrho S.radius_upper F.density_pos hB₀p hL S.density_lower hradius
    have hlocalS := hlocal S.selected.card (family S) F.δ S.rho S.s F.A
      hselected hδ S.radius_lower S.radius_upper S.density_pos F.cap_ge_one
      (family_admissible S F.admissible) (family_comparable S)
      (family_cap_bound S F.cap_bound) (fun i => S.centers (index S i))
      (family_ball S) (family_two_ends S)
    have hsubset : ((family S).unionCells.card:ℝ) ≤ (F.family.unionCells.card:ℝ) :=
      Nat.cast_le.mpr (Finset.card_le_card (family_union_subset S))
    have hstep : (cLocal*F.A⁻¹*F.δ^(m-D+eps/2))*(a*L^(-(b*q))*F.lam^C)*
        (S.selected.card:ℝ) ≤ (F.family.unionCells.card:ℝ) := by
      have hh := mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_left hnum (by positivity : 0 ≤ cLocal*F.A⁻¹*F.δ^(m-D+eps/2)))
        (Nat.cast_nonneg S.selected.card)
      apply hh.trans
      convert hlocalS.trans hsubset using 1
      ring
    have hpopulation := selected_population S hδ hbeta.le
    have hlogProduct : L^(-(b*q+2)) = L^(-(b*q))*L^(-(2:ℝ)) := by
      rw [← Real.rpow_add hL]
      congr 1
      ring
    have hcombined : cLocal*a*populationCoefficient beta*F.A⁻¹*F.δ^(m-D+eps/2)*
        F.lam^C*L^(-(b*q+2))*(F.M:ℝ) ≤ (F.family.unionCells.card:ℝ) := by
      calc
        _ = ((cLocal*F.A⁻¹*F.δ^(m-D+eps/2))*(a*L^(-(b*q))*F.lam^C))*
            (populationCoefficient beta*L^(-(2:ℝ))*(F.M:ℝ)) := by
          rw [hlogProduct]
          ring
        _ ≤ ((cLocal*F.A⁻¹*F.δ^(m-D+eps/2))*(a*L^(-(b*q))*F.lam^C))*
            (S.selected.card:ℝ) := mul_le_mul_of_nonneg_left hpopulation (by positivity [F.density_pos])
        _ ≤ _ := hstep
    have hlogs := hlog F.δ hδ F.scale_le_one
    have hδpow : F.δ^(m-D+eps) = F.δ^(m-D+eps/2)*F.δ^(eps/2) := by
      rw [← Real.rpow_add hδ]
      congr 1
      ring
    calc
      _ = (cLocal*a*populationCoefficient beta*F.A⁻¹*F.δ^(m-D+eps/2)*F.lam^C*(F.M:ℝ))*
          (ell*F.δ^(eps/2)) := by dsimp [cFine]; rw [hδpow]; ring
      _ ≤ (cLocal*a*populationCoefficient beta*F.A⁻¹*F.δ^(m-D+eps/2)*F.lam^C*(F.M:ℝ))*
          L^(-(b*q+2)) := mul_le_mul_of_nonneg_left hlogs (by positivity [F.density_pos])
      _ = _ := by ring
      _ ≤ _ := hcombined
  let cCoarse := 1/(ProjectiveGeometry.packingConstant k*max 1 (cutoff^(1-D+eps)))
  have hcCoarse : 0 < cCoarse := by
    have hh := ProjectiveGeometry.packingConstant_ge_one k
    dsimp [cCoarse]
    positivity
  refine ⟨min cFine cCoarse,lt_min hcFine hcCoarse,?_⟩
  intro F hends
  have hcoef : 0 ≤ F.A⁻¹*F.δ^(m-D+eps)*F.lam^C*F.M := by
    have hAp := zero_lt_one.trans_le F.cap_ge_one
    positivity [F.scale_pos,F.density_pos]
  by_cases hsmall : F.δ ≤ cutoff
  · have hh := mul_le_mul_of_nonneg_right (min_le_left cFine cCoarse) hcoef
    apply le_trans ?_ (hfine F hsmall hends)
    simpa only [mul_assoc] using hh
  · have hh := mul_le_mul_of_nonneg_right (min_le_right cFine cCoarse) hcoef
    apply le_trans ?_ (CoarseBounds.coarse_configuration_bound (d:=D) (eps:=eps) hcutoff hC geom F (le_of_not_ge hsmall))
    simpa only [mul_assoc] using hh

end
end KakeyaFormal.LogarithmicTwoEnds
