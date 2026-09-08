import MeasurableSeedGeometry
import MeasurableDensityTrimming
import DensityLogNormalization

/-! Continuous all-angle square-root-cap estimate with fixed or logarithmic
upper/lower density ratios. Actual measurable subsets normalize the density;
all original positions, directions, cap coefficients and union are preserved. -/
namespace KakeyaFormal.MeasurableSeedDensity
open MeasureTheory Set DensityLogNormalization
open scoped ENNReal
noncomputable section
open Classical

/-- Source (4.4) with independent logarithmic lower and upper density losses,
fixed physical width and positive direction-separation constants. No actual
coefficient B>=1 is required of the original two-ends hypothesis. -/
theorem logarithmic_density_seed (k : ℕ)
    {width separation alpha B₀ c₀ C₀ b ell u m : ℝ}
    (hseparation : 0 < separation) (halpha : 0 < alpha) (hB₀ : 1 ≤ B₀)
    (hc₀ : 0 < c₀) (_hC₀ : 0 < C₀) (hb : 0 ≤ b) (hell : 0 ≤ ell) (hu : 0 ≤ u)
    (hm : 1 < m) :
    ∃ c P : ℝ, 0 < c ∧ 0 ≤ P ∧
      ∀ M : ℕ, ∀ F : TubeFamily (k+2) M, ∀ Y : Fin M → Set (Space (k+2)),
      ∀ δ sigma A : ℝ, 0 < δ → δ ≤ 1 → 0 < sigma → sigma ≤ 1 → 1 ≤ A →
      (∀ i, MeasurableSet (Y i)) → (∀ i, Y i ⊆ (F.tube i).carrier (width*δ)) →
      (∀ i, c₀*(Real.log (2/δ))^(-ell)*sigma*δ^(k+1) ≤ volume.real (Y i)) →
      (∀ i, volume.real (Y i) ≤ C₀*(Real.log (2/δ))^u*sigma*δ^(k+1)) →
      F.Separated (separation*δ) → F.CapBound δ m A →
      (∀ i x r, δ ≤ r → r ≤ 1 → volume.real (Y i ∩ Metric.closedBall x r) ≤
        (B₀*(Real.log (2/δ))^b)*r^alpha*volume.real (Y i)) →
      c*(Real.sqrt A)⁻¹*(Real.log (2/δ))^(-P)*sigma^2*(M:ℝ)*δ^((m-3)/2) ≤
        volume.real (⋃ i, Y i)/δ^(k+2) := by
  let a₀ := lowerFactor c₀ ell
  have ha₀ : 0 < a₀ := lowerFactor_pos hc₀
  let t := b+u+ell
  have ht : 0 ≤ t := by dsimp [t]; linarith
  let D := B₀*C₀/a₀
  let BF := twoEndsFactor D t
  have hBF : 1 ≤ BF := twoEndsFactor_ge_one D t
  obtain ⟨c,P,hc,hP,hmain⟩ := MeasurableSeedGeometry.natural_logarithmic_seed k
    (width:=width) hseparation halpha hBF ht hm
  refine ⟨c*a₀^2,P+2*ell,by positivity,by linarith,?_⟩
  intro M F Y δ sigma A hδ hδ1 hsigma hsigma1 hA hY hsub hlower hupper hsep hcap hends
  let L := Real.log (2/δ)
  have hlog2 : 0 < Real.log (2:ℝ) := Real.log_pos (by norm_num)
  have hLlower : Real.log 2 ≤ L := by
    apply Real.log_le_log (by norm_num : (0:ℝ) < 2)
    apply (le_div_iff₀ hδ).mpr
    nlinarith
  have hL : 0 < L := hlog2.trans_le hLlower
  let lam := a₀*L^(-ell)*sigma
  have hlam := normalized_density hc₀ hell hLlower hsigma hsigma1
  change 0 < lam ∧ lam ≤ 1 at hlam
  let a := lam*δ^(k+1)
  have ha : 0 < a := mul_pos hlam.1 (pow_pos hδ _)
  have halower (i) : a ≤ volume.real (Y i) := by
    have hh := mul_le_mul_of_nonneg_right (lowerFactor_le (c₀:=c₀) (ell:=ell)).1
      (by positivity : 0 ≤ L^(-ell)*sigma*δ^(k+1))
    apply le_trans ?_ (hlower i)
    convert hh using 1 <;> first | rfl | (dsimp [a,lam,a₀,L]; ring)
  obtain ⟨O⟩ := MeasurableDensityTrimming.construct F Y hY hsub ha.le halower
  let BN := max 1 (D*L^t)
  have hBN : 1 ≤ BN := le_max_left _ _
  have hBNbudget : BN ≤ BF*L^t := max_one_budget D ht hLlower
  have hlowerNew (i) : lam*δ^(k+1) ≤ volume.real (O.shading i) := by
    rw [O.exact_volume]
  have hupperNew (i) : volume.real (O.shading i) ≤ 2*lam*δ^(k+1) := by
    rw [O.exact_volume]
    dsimp [a]
    nlinarith [mul_pos hlam.1 (pow_pos hδ (k+1))]
  have hnewEnds : ∀ i x r, δ ≤ r → r ≤ 1 →
      volume.real (O.shading i ∩ Metric.closedBall x r) ≤
        BN*r^alpha*volume.real (O.shading i) := by
    intro i x r hr hr1
    have hBpos : 0 ≤ B₀*L^b := by positivity
    have hh := O.two_ends_upper ha hBpos hsub hupper i x (hδ.trans_le hr).le (hends i x r hr hr1)
    have heq : (B₀*L^b)*(C₀*L^u*sigma*δ^(k+1))/a = D*L^t := by
      simpa only [a,lam,D,t] using density_ratio_identity hL ha₀ hsigma hδ (k+1) B₀ C₀ b u ell
    rw [heq] at hh
    have hm := mul_le_mul_of_nonneg_right (le_max_right (1:ℝ) (D*L^t))
      (Real.rpow_nonneg (hδ.trans_le hr).le alpha)
    have hm' := mul_le_mul_of_nonneg_right hm
      (measureReal_nonneg (μ:=volume) (s:=O.shading i))
    exact hh.trans hm'
  have hbound := hmain M F O.shading δ lam BN A hδ hδ1 hlam.1 hlam.2 hBN hA hBNbudget
    O.measurable O.subset_carrier hlowerNew hupperNew hsep hcap hnewEnds
  have hunion := div_le_div_of_nonneg_right (O.union_volume_le hsub) (pow_pos hδ (k+2)).le
  apply (le_of_eq ?_).trans (hbound.trans hunion)
  have hid := density_loss_identity hL a₀ sigma P ell
  change L^(-P)*lam^2 = a₀^2*L^(-(P+2*ell))*sigma^2 at hid
  calc
    _ = (c*(Real.sqrt A)⁻¹*(M:ℝ)*δ^((m-3)/2))*(a₀^2*L^(-(P+2*ell))*sigma^2) := by
      dsimp [L]
      ring
    _ = (c*(Real.sqrt A)⁻¹*(M:ℝ)*δ^((m-3)/2))*(L^(-P)*lam^2) := by rw [hid]
    _ = c*(Real.sqrt A)⁻¹*(Real.log (2/δ))^(-P)*lam^2*(M:ℝ)*δ^((m-3)/2) := by
      dsimp only [L]
      ring

/-- The ordinary fixed comparable-density formulation is included by setting
both density-logarithm losses to zero; c0,C0 are arbitrary fixed positives. -/
theorem comparable_density_seed (k : ℕ)
    {width separation alpha B₀ c₀ C₀ b m : ℝ}
    (hseparation : 0 < separation) (halpha : 0 < alpha) (hB₀ : 1 ≤ B₀)
    (hc₀ : 0 < c₀) (hC₀ : 0 < C₀) (hb : 0 ≤ b) (hm : 1 < m) :
    ∃ c P : ℝ, 0 < c ∧ 0 ≤ P ∧
      ∀ M : ℕ, ∀ F : TubeFamily (k+2) M, ∀ Y : Fin M → Set (Space (k+2)),
      ∀ δ sigma A : ℝ, 0 < δ → δ ≤ 1 → 0 < sigma → sigma ≤ 1 → 1 ≤ A →
      (∀ i, MeasurableSet (Y i)) → (∀ i, Y i ⊆ (F.tube i).carrier (width*δ)) →
      (∀ i, c₀*sigma*δ^(k+1) ≤ volume.real (Y i)) →
      (∀ i, volume.real (Y i) ≤ C₀*sigma*δ^(k+1)) →
      F.Separated (separation*δ) → F.CapBound δ m A →
      (∀ i x r, δ ≤ r → r ≤ 1 → volume.real (Y i ∩ Metric.closedBall x r) ≤
        (B₀*(Real.log (2/δ))^b)*r^alpha*volume.real (Y i)) →
      c*(Real.sqrt A)⁻¹*(Real.log (2/δ))^(-P)*sigma^2*(M:ℝ)*δ^((m-3)/2) ≤
        volume.real (⋃ i, Y i)/δ^(k+2) := by
  simpa only [neg_zero,Real.rpow_zero,mul_one] using
    logarithmic_density_seed k (width:=width) hseparation halpha hB₀ hc₀ hC₀ hb
      (show (0:ℝ) ≤ 0 by norm_num) (show (0:ℝ) ≤ 0 by norm_num) hm

end
end KakeyaFormal.MeasurableSeedDensity
