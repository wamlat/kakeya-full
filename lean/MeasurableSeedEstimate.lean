import MeasurableAngularHairbrush
import MeasurableSeedLogLoss

/-! Actual continuous all-angle square-root-cap seed for measurable shadings.
The angular pieces, weighted selection, measurable realization and hairbrush
are proved, with constants uniform in scale, density, cap coefficient and positions. -/
namespace KakeyaFormal.MeasurableSeedEstimate
open MeasureTheory Set AngularSeedPieces AngularSeedHairbrush AngularSeedLogLoss
open HairbrushScales
open scoped ENNReal
noncomputable section
open Classical

/-- The actual arbitrary-measurable depth theorem with its exact uniform
logarithmic and square-root-cap coefficient. -/
theorem logarithmic_seed_with_pieces {k M : ℕ} (F : TubeFamily (k+2) M)
    (Y : Fin M → Set (Space (k+2))) {δ beta lam alpha B B₀ b m A : ℝ}
    (P : MeasurableAngularPieces.Pieces F Y δ beta)
    (hδ : 0 < δ) (hlam : 0 < lam) (hlam1 : lam ≤ 1)
    (halpha : 0 < alpha) (hbeta : 0 < beta) (hbetaS : beta ≤ (m-1)/2)
    (hB : 1 ≤ B) (hB₀ : 1 ≤ B₀) (hm : 1 ≤ m) (hA : 1 ≤ A)
    (hBB : B ≤ B₀*(seedLog δ)^b)
    (hY : ∀ i, MeasurableSet (Y i)) (hsub : ∀ i, Y i ⊆ (F.tube i).carrier δ)
    (hlower : ∀ i, lam*δ^(k+1) ≤ volume.real (Y i))
    (hupper : ∀ i, volume.real (Y i) ≤ 2*lam*δ^(k+1))
    (hsep : F.Separated δ) (hcap : F.CapBound δ m A)
    (hends : ∀ i x r, δ ≤ r → r ≤ 1 → volume.real (Y i ∩ Metric.closedBall x r) ≤
      B*r^alpha*volume.real (Y i)) :
    MeasurableSeedLogLoss.uniformConstant k alpha beta B₀ m/Real.sqrt A*
      (seedLog δ)^(-uniformLoss k alpha beta b)*lam^2*(M:ℝ)*δ^((m-3)/2) ≤
        volume.real (⋃ i, Y i)/δ^(k+2) := by
  have hraw := MeasurableAngularHairbrush.measurable_seed_at_depth F Y P hδ hlam hlam1
    halpha hbeta hbetaS hB hm hA hY hsub hlower hupper hsep hcap hends
  have hpre := MeasurableSeedLogLoss.uniform_prefactor k P.J hδ P.lower_scale P.upper_scale
    P.depth halpha hbeta hB hB₀ hm hA hBB
  have hh := mul_le_mul_of_nonneg_right hpre
    (by positivity : 0 ≤ lam^2*(M:ℝ)*δ^((m-3)/2))
  apply le_trans ?_ hraw
  convert hh using 1
  · ring
  · unfold MeasurableSeedLogLoss.depthConstant MeasurableAngularHairbrush.seedConstant
    ring

/-- Every angular piece is constructed internally. The statement applies to
arbitrary measurable sets inside actual tube carriers, including unbounded
families of positions; no grid cells or supplied broadness premise is used. -/
theorem logarithmic_seed (k : ℕ) {alpha B₀ b m : ℝ}
    (halpha : 0 < alpha) (hB₀ : 1 ≤ B₀) (hb : 0 ≤ b) (hm : 1 < m) :
    ∃ c P : ℝ, 0 < c ∧ 0 ≤ P ∧
      ∀ M : ℕ, ∀ F : TubeFamily (k+2) M, ∀ Y : Fin M → Set (Space (k+2)),
      ∀ δ lam B A : ℝ, 0 < δ → δ ≤ 1 → 0 < lam → lam ≤ 1 → 1 ≤ B → 1 ≤ A →
      B ≤ B₀*(seedLog δ)^b →
      (∀ i, MeasurableSet (Y i)) → (∀ i, Y i ⊆ (F.tube i).carrier δ) →
      (∀ i, lam*δ^(k+1) ≤ volume.real (Y i)) →
      (∀ i, volume.real (Y i) ≤ 2*lam*δ^(k+1)) →
      F.Separated δ → F.CapBound δ m A →
      (∀ i x r, δ ≤ r → r ≤ 1 → volume.real (Y i ∩ Metric.closedBall x r) ≤
        B*r^alpha*volume.real (Y i)) →
      c*(Real.sqrt A)⁻¹*(seedLog δ)^(-P)*lam^2*(M:ℝ)*δ^((m-3)/2) ≤
        volume.real (⋃ i, Y i)/δ^(k+2) := by
  let beta : ℝ := min (1/2) ((m-1)/4)
  have hbeta : 0 < beta := lt_min (by norm_num) (by linarith)
  have hbetaS : beta ≤ (m-1)/2 := by
    have h := min_le_right (1/2:ℝ) ((m-1)/4)
    dsimp only [beta]
    linarith
  refine ⟨MeasurableSeedLogLoss.uniformConstant k alpha beta B₀ m,uniformLoss k alpha beta b,
    MeasurableSeedLogLoss.uniformConstant_pos k hbeta hB₀ hm.le,
    uniformLoss_nonneg k halpha hbeta hb,?_⟩
  intro M F Y δ lam B A hδ hδ1 hlam hlam1 hB hA hBB hY hsub hlower hupper hsep hcap hends
  by_cases hM : 0 < M
  · have hfin (i) : volume (Y i) ≠ ∞ :=
      measure_ne_top_of_subset (hsub i) (TubeVolume.carrier_finite _ _)
    obtain ⟨P⟩ := MeasurableAngularPieces.exists_pieces F hM Y hY hfin hδ hδ1 hbeta.le
    simpa only [div_eq_mul_inv] using logarithmic_seed_with_pieces F Y P hδ hlam hlam1
      halpha hbeta hbetaS hB hB₀ hm.le hA hBB hY hsub hlower hupper hsep hcap hends
  · have hz : M = 0 := by omega
    simp only [hz,Nat.cast_zero,mul_zero,zero_mul]
    exact div_nonneg measureReal_nonneg (pow_pos hδ _).le

/-- Literal natural logarithm as in (4.4), still on the original measurable
union with the exact normalized-volume scale exponent. -/
theorem natural_logarithmic_seed (k : ℕ) {alpha B₀ b m : ℝ}
    (halpha : 0 < alpha) (hB₀ : 1 ≤ B₀) (hb : 0 ≤ b) (hm : 1 < m) :
    ∃ c P : ℝ, 0 < c ∧ 0 ≤ P ∧
      ∀ M : ℕ, ∀ F : TubeFamily (k+2) M, ∀ Y : Fin M → Set (Space (k+2)),
      ∀ δ lam B A : ℝ, 0 < δ → δ ≤ 1 → 0 < lam → lam ≤ 1 → 1 ≤ B → 1 ≤ A →
      B ≤ B₀*(Real.log (2/δ))^b →
      (∀ i, MeasurableSet (Y i)) → (∀ i, Y i ⊆ (F.tube i).carrier δ) →
      (∀ i, lam*δ^(k+1) ≤ volume.real (Y i)) →
      (∀ i, volume.real (Y i) ≤ 2*lam*δ^(k+1)) →
      F.Separated δ → F.CapBound δ m A →
      (∀ i x r, δ ≤ r → r ≤ 1 → volume.real (Y i ∩ Metric.closedBall x r) ≤
        B*r^alpha*volume.real (Y i)) →
      c*(Real.sqrt A)⁻¹*(Real.log (2/δ))^(-P)*lam^2*(M:ℝ)*δ^((m-3)/2) ≤
        volume.real (⋃ i, Y i)/δ^(k+2) := by
  obtain ⟨c,P,hc,hP,hmain⟩ := logarithmic_seed k halpha hB₀ hb hm
  have hC : 0 < (3:ℝ)/Real.log 2 := div_pos (by norm_num) (Real.log_pos (by norm_num))
  refine ⟨c*((3:ℝ)/Real.log 2)^(-P),P,mul_pos hc (Real.rpow_pos_of_pos hC _),hP,?_⟩
  intro M F Y δ lam B A hδ hδ1 hlam hlam1 hB hA hBB hY hsub hlower hupper hsep hcap hends
  have hL : 0 < Real.log (2/δ) := Real.log_pos ((lt_div_iff₀ hδ).mpr (by linarith))
  have hLS : 0 < seedLog δ := zero_lt_one.trans_le (seedLog_ge_one hδ hδ1)
  have hBseed : B ≤ B₀*(seedLog δ)^b := hBB.trans
    (mul_le_mul_of_nonneg_left (Real.rpow_le_rpow hL.le
      (AngularSeedSqrtCap.natural_log_le_seedLog hδ hδ1) hb) (by linarith))
  have hs := Real.rpow_le_rpow_of_nonpos hLS (AngularSeedEstimate.seedLog_upper hδ hδ1) (neg_nonpos.mpr hP)
  rw [Real.mul_rpow hC.le hL.le] at hs
  have hfac : 0 ≤ c*(Real.sqrt A)⁻¹*lam^2*(M:ℝ)*δ^((m-3)/2) := by positivity
  have hh := mul_le_mul_of_nonneg_left hs hfac
  calc
    _ = (c*(Real.sqrt A)⁻¹*lam^2*(M:ℝ)*δ^((m-3)/2))*
        (((3:ℝ)/Real.log 2)^(-P)*(Real.log (2/δ))^(-P)) := by ring
    _ ≤ _ := hh
    _ = c*(Real.sqrt A)⁻¹*(seedLog δ)^(-P)*lam^2*(M:ℝ)*δ^((m-3)/2) := by ring
    _ ≤ _ := hmain M F Y δ lam B A hδ hδ1 hlam hlam1 hB hA hBseed hY hsub hlower hupper hsep hcap hends

end
end KakeyaFormal.MeasurableSeedEstimate
