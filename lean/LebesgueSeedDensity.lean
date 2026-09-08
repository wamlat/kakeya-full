import LebesgueRepresentatives
import MeasurableSeedDensityLengths

/-! The continuous density-square, square-root-cap seed holds for arbitrary
Lebesgue measurable original shadings. Exact Borel subset representatives
preserve lower/upper densities, every physical two-ends test and union volume. -/
namespace KakeyaFormal.LebesgueSeedDensity
open MeasureTheory SamplingGeometry
noncomputable section

theorem logarithmic_density_seed (k : ℕ)
    {width upperLength separation alpha B₀ c₀ C₀ b ell u m : ℝ}
    (hLength : 0 < upperLength) (hseparation : 0 < separation) (halpha : 0 < alpha) (hB₀ : 1 ≤ B₀)
    (hc₀ : 0 < c₀) (hC₀ : 0 < C₀) (hb : 0 ≤ b) (hell : 0 ≤ ell) (hu : 0 ≤ u)
    (hm : 1 < m) :
    ∃ c P : ℝ, 0 < c ∧ 0 ≤ P ∧
      ∀ M : ℕ, ∀ F : TubeFamily (k+2) M, ∀ Y : Fin M → Set (Space (k+2)), ∀ length : Fin M → ℝ,
      ∀ δ sigma A : ℝ, 0 < δ → δ ≤ 1 → 0 < sigma → sigma ≤ 1 → 1 ≤ A →
      (∀ i, length i ≤ upperLength) →
      (∀ i, NullMeasurableSet (Y i) (volume : Measure (Space (k+2)))) →
      (∀ i, Y i ⊆ lengthCarrier (F.tube i) (length i) (width*δ)) →
      (∀ i, c₀*(Real.log (2/δ))^(-ell)*sigma*δ^(k+1) ≤ volume.real (Y i)) →
      (∀ i, volume.real (Y i) ≤ C₀*(Real.log (2/δ))^u*sigma*δ^(k+1)) →
      F.Separated (separation*δ) → F.CapBound δ m A →
      (∀ i x r, δ ≤ r → r ≤ 1 → volume.real (Y i ∩ Metric.closedBall x r) ≤
        (B₀*(Real.log (2/δ))^b)*r^alpha*volume.real (Y i)) →
      c*(Real.sqrt A)⁻¹*(Real.log (2/δ))^(-P)*sigma^2*(M:ℝ)*δ^((m-3)/2) ≤
        volume.real (⋃ i, Y i)/δ^(k+2) := by
  obtain ⟨c,P,hc,hP,hmain⟩ := MeasurableSeedDensityLengths.logarithmic_density_seed
    k (width:=width) hLength hseparation halpha hB₀ hc₀ hC₀ hb hell hu hm
  refine ⟨c,P,hc,hP,?_⟩
  intro M F Y length δ sigma A hδ hδ1 hsigma hsigma1 hA hlength hY hsub hlower hupper hsep hcap hends
  obtain ⟨O⟩ := LebesgueRepresentatives.construct (volume : Measure (Space (k+2)))
    Y Y hY hY (fun _ => Set.Subset.rfl)
  have hlower' : ∀ i, c₀*(Real.log (2/δ))^(-ell)*sigma*δ^(k+1) ≤ volume.real (O.full i) := by
    intro i
    rw [O.full_real]
    exact hlower i
  have hupper' : ∀ i, volume.real (O.full i) ≤ C₀*(Real.log (2/δ))^u*sigma*δ^(k+1) := by
    intro i
    rw [O.full_real]
    exact hupper i
  have hends' : ∀ i x r, δ ≤ r → r ≤ 1 → volume.real (O.full i ∩ Metric.closedBall x r) ≤
      (B₀*(Real.log (2/δ))^b)*r^alpha*volume.real (O.full i) := by
    intro i x r hr hr1
    rw [O.full_inter_real,O.full_real]
    exact hends i x r hr hr1
  have hbnd := hmain M F O.full length δ sigma A hδ hδ1 hsigma hsigma1 hA hlength
    O.full_measurable (fun i => (O.full_subset i).trans (hsub i)) hlower' hupper' hsep hcap hends'
  rwa [O.full_union_real] at hbnd

theorem comparable_density_seed (k : ℕ)
    {width upperLength separation alpha B₀ c₀ C₀ b m : ℝ}
    (hLength : 0 < upperLength) (hseparation : 0 < separation) (halpha : 0 < alpha) (hB₀ : 1 ≤ B₀)
    (hc₀ : 0 < c₀) (hC₀ : 0 < C₀) (hb : 0 ≤ b) (hm : 1 < m) :
    ∃ c P : ℝ, 0 < c ∧ 0 ≤ P ∧
      ∀ M : ℕ, ∀ F : TubeFamily (k+2) M, ∀ Y : Fin M → Set (Space (k+2)), ∀ length : Fin M → ℝ,
      ∀ δ sigma A : ℝ, 0 < δ → δ ≤ 1 → 0 < sigma → sigma ≤ 1 → 1 ≤ A →
      (∀ i, length i ≤ upperLength) →
      (∀ i, NullMeasurableSet (Y i) (volume : Measure (Space (k+2)))) →
      (∀ i, Y i ⊆ lengthCarrier (F.tube i) (length i) (width*δ)) →
      (∀ i, c₀*sigma*δ^(k+1) ≤ volume.real (Y i)) →
      (∀ i, volume.real (Y i) ≤ C₀*sigma*δ^(k+1)) →
      F.Separated (separation*δ) → F.CapBound δ m A →
      (∀ i x r, δ ≤ r → r ≤ 1 → volume.real (Y i ∩ Metric.closedBall x r) ≤
        (B₀*(Real.log (2/δ))^b)*r^alpha*volume.real (Y i)) →
      c*(Real.sqrt A)⁻¹*(Real.log (2/δ))^(-P)*sigma^2*(M:ℝ)*δ^((m-3)/2) ≤
        volume.real (⋃ i, Y i)/δ^(k+2) := by
  simpa only [neg_zero,Real.rpow_zero,mul_one] using
    logarithmic_density_seed k (width:=width) hLength hseparation halpha hB₀ hc₀ hC₀ hb
      (show (0:ℝ) ≤ 0 by norm_num) (show (0:ℝ) ≤ 0 by norm_num) hm

end
end KakeyaFormal.LebesgueSeedDensity
