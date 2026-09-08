import WideTwoEndsEstimate
import LogarithmicTwoEnds

/-! Actual fixed-multiple row normalization for the ORIGINAL logarithmic
two-ends coefficient. The same indices and original cells are retained;
the fixed analytic constant is chosen before the original scale and density. -/
namespace KakeyaFormal.WideLogarithmicTwoEnds
open Finset WideTwoEndsEstimate
noncomputable section
open Classical

/-- Arbitrary fixed positive density multiples, with the same density power
and actual original logarithmic two-ends budget. There is no per-configuration
assumption that the budget B0*log(2/delta)^b is at least one. -/
theorem estimate {k : ℕ} {m D C : ℝ}
    (hestimate : TwoEndsDiscreteEstimate (k+1) m D C)
    (hm : 0 ≤ m) (hC : 1 ≤ C)
    (geom : Normalization) (c₀ C₀ B₀ alpha b eps : ℝ)
    (hc₀ : 0 < c₀) (hC₀ : 0 < C₀) (hB₀ : 1 ≤ B₀)
    (halpha : 0 < alpha) (hb : 0 ≤ b) (heps : 0 < eps) :
    ∃ c : ℝ, 0 < c ∧ ∀ {M : ℕ} (F : TubeFamily (k+1) M) {δ lam A : ℝ},
      0 < δ → δ ≤ 1 → 0 < lam → lam ≤ 1 → 1 ≤ A →
      F.Admissible geom.width δ → F.Separated (geom.separation*δ) →
      F.Bounded geom.radius → F.CapBound δ m A →
      (∀ i, c₀*lam/δ ≤ ((F.shade i).card:ℝ)) →
      (∀ i, ((F.shade i).card:ℝ) ≤ C₀*lam/δ) →
      F.FullTwoEnds δ (B₀*(Real.log (2/δ))^b) alpha →
      c*A⁻¹*δ^(m-D+eps)*lam^C*(M:ℝ) ≤ (F.unionCells.card:ℝ) := by
  let a := lowerFactor c₀
  have ha : 0 < a := lowerFactor_pos hc₀
  let BN := max 1 (B₀*C₀/a)
  obtain ⟨c,hc,hbound⟩ := LogarithmicTwoEnds.estimate hestimate hm hC
    geom BN alpha b eps (le_max_left _ _) halpha hb heps
  refine ⟨c*(a/2)^C,by positivity,?_⟩
  intro M F δ lam A hδ hδ1 hlam hlam1 hA hadm hsep hbounded hcap hlo hhi hends
  let L := Real.log (2/δ)
  have hL : 0 < L := Real.log_pos ((lt_div_iff₀ hδ).mpr (by linarith))
  have hB₀p : 0 < B₀ := zero_lt_one.trans_le hB₀
  obtain ⟨G,nu,hnu,hnu1,hnuLow,htube,hsub,hcomp,hcounts⟩ :=
    normalize_rows F hδ hδ1 hlam hlam1 hc₀ hC₀ hlo hhi
  have hGends : G.FullTwoEnds δ (BN*L^b) alpha := by
    intro i x r hr hr1
    have hcell : ((G.shade i).filter (fun z => dist (cellCenter δ z) x ≤ r)).card ≤
        ((F.shade i).filter (fun z => dist (cellCenter δ z) x ≤ r)).card :=
      card_le_card (filter_subset_filter _ (hsub i))
    have hball := hends i x r hr hr1
    have hh := mul_le_mul_of_nonneg_left (hcounts i)
      (show 0 ≤ (B₀*L^b)*r^alpha by positivity [hδ.trans_le hr])
    have hBN := mul_le_mul_of_nonneg_right (le_max_right (1:ℝ) (B₀*C₀/a))
      (show 0 ≤ L^b*r^alpha*((G.shade i).card:ℝ) by positivity [hδ.trans_le hr])
    calc
      _ ≤ (((F.shade i).filter (fun z => dist (cellCenter δ z) x ≤ r)).card:ℝ) :=
        Nat.cast_le.mpr hcell
      _ ≤ (B₀*L^b)*r^alpha*((F.shade i).card:ℝ) := hball
      _ ≤ (B₀*L^b)*r^alpha*((C₀/a)*((G.shade i).card:ℝ)) := hh
      _ ≤ (BN*L^b)*r^alpha*((G.shade i).card:ℝ) := by
        simpa only [BN,div_eq_mul_inv,mul_assoc,mul_left_comm,mul_comm] using hBN
  let V : ShadedConfiguration (k+1) geom m := {
    M:=M, δ:=δ, lam:=nu, A:=A, family:=G,
    scale_pos:=hδ, scale_le_one:=hδ1, density_pos:=hnu, density_le_one:=hnu1,
    cap_ge_one:=hA,
    admissible:=fun i z hz => by rw [htube]; exact hadm i z (hsub i hz),
    separated:=by simpa only [TubeFamily.Separated,htube] using hsep,
    bounded:=by simpa only [TubeFamily.Bounded,htube] using hbounded,
    cap_bound:=by simpa only [TubeFamily.CapBound,htube] using hcap,
    comparable:=hcomp }
  have hGU : G.unionCells ⊆ F.unionCells := by
    intro z hz
    obtain ⟨i,_,hi⟩ := mem_biUnion.mp hz
    exact F.shade_subset_union i (hsub i hi)
  have hpow := Real.rpow_le_rpow (by positivity : 0 ≤ (a/2)*lam)
    hnuLow (zero_le_one.trans hC)
  rw [Real.mul_rpow (by positivity : 0 ≤ a/2) hlam.le] at hpow
  have hfactor : 0 ≤ c*A⁻¹*δ^(m-D+eps)*(M:ℝ) := by positivity
  have hscaled := mul_le_mul_of_nonneg_left hpow hfactor
  have hfinal := hbound V hGends
  have hunion : (G.unionCells.card:ℝ) ≤ (F.unionCells.card:ℝ) :=
    Nat.cast_le.mpr (card_le_card hGU)
  calc
    _ = (c*A⁻¹*δ^(m-D+eps)*(M:ℝ))*((a/2)^C*lam^C) := by ring
    _ ≤ (c*A⁻¹*δ^(m-D+eps)*(M:ℝ))*nu^C := hscaled
    _ ≤ (G.unionCells.card:ℝ) := by
      simpa only [V,mul_assoc,mul_left_comm,mul_comm] using hfinal
    _ ≤ _ := hunion

end
end KakeyaFormal.WideLogarithmicTwoEnds
