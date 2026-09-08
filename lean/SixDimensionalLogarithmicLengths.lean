import LogarithmicLengthEstimates
import TwoEndsPivot

/-! First-step Lemma 6 with all fixed original geometric and comparable-row
conventions. The actual old axes, row labels and union are the conclusion's
data; logarithmic two ends is measured at the ORIGINAL scale. -/
namespace KakeyaFormal.SixDimensionalLogarithmicLengths
noncomputable section

/-- Arbitrary fixed comparable-density multiples and bounded individual
lengths, with no cap premise. Separation supplies the fixed ambient cap bound. -/
theorem cap_free (geom : Normalization) (lengthUpper c₀ C₀ B₀ alpha b eps : ℝ)
    (hc₀ : 0 < c₀) (hC₀ : 0 < C₀) (hB₀ : 1 ≤ B₀)
    (ha : 0 < alpha) (hb : 0 ≤ b) (heps : 0 < eps) :
    ∃ c : ℝ, 0 < c ∧ ∀ {M : ℕ} (F : TubeFamily 6 M) (lengths : Fin M → ℝ)
      {δ lam : ℝ},
      0 < δ → δ ≤ 1 → 0 < lam → lam ≤ 1 →
      (∀ i, lengths i ≤ lengthUpper) →
      (∀ i z, z ∈ F.shade i → cellCenter δ z ∈
        SamplingGeometry.lengthCarrier (F.tube i) (lengths i) (geom.width*δ)) →
      F.Separated (geom.separation*δ) → F.Bounded geom.radius →
      (∀ i, c₀*lam/δ ≤ ((F.shade i).card:ℝ)) →
      (∀ i, ((F.shade i).card:ℝ) ≤ C₀*lam/δ) →
      F.FullTwoEnds δ (B₀*(Real.log (2/δ))^b) alpha →
      c*δ^((7:ℝ)/8+eps)*lam^((15:ℝ)/4)*(M:ℝ) ≤ (F.unionCells.card:ℝ) := by
  let A₀ := ProjectiveGeometry.fullDirectionCoefficient 5 geom.separation
  have hA₀ : 1 ≤ A₀ := ProjectiveGeometry.fullDirectionCoefficient_ge_one 5 geom.separation_pos
  obtain ⟨c,hc,hestimate⟩ := LogarithmicLengthEstimates.estimate (k:=5)
    TwoEndsPivot.six_dimensional (by norm_num) (by norm_num)
    geom lengthUpper c₀ C₀ B₀ alpha b eps hc₀ hC₀ hB₀ ha hb heps
  refine ⟨c*A₀⁻¹,mul_pos hc (inv_pos.mpr (zero_lt_one.trans_le hA₀)),?_⟩
  intro M F lengths δ lam hδ hδ1 hlam hlam1 hlength hadm hsep hbounded hlo hhi hends
  have hcap : F.CapBound δ 5 A₀ := by
    simpa only [Nat.cast_ofNat] using
      ProjectiveGeometry.separated_tube_family_cap_bound (k:=5) F hδ geom.separation_pos hsep
  have h := hestimate F lengths hδ hδ1 hlam hlam1 hA₀ hlength hadm hsep hbounded hcap hlo hhi hends
  norm_num at h
  exact h

/-- Literal first-step (25), including its original fixed width/length/
separation and lower/upper density conventions. The constant precedes N,
lambda, every individual length, every row and the whole original family. -/
theorem source_notation (geom : Normalization) (lengthUpper c₀ C₀ B₀ alpha b eps : ℝ)
    (hc₀ : 0 < c₀) (hC₀ : 0 < C₀) (hB₀ : 1 ≤ B₀)
    (ha : 0 < alpha) (hb : 0 ≤ b) (heps : 0 < eps) :
    ∃ c : ℝ, 0 < c ∧ ∀ {M : ℕ} (F : TubeFamily 6 M) (lengths : Fin M → ℝ)
      {N lam : ℝ},
      1 ≤ N → 0 < lam → lam ≤ 1 →
      (∀ i, lengths i ≤ lengthUpper) →
      (∀ i z, z ∈ F.shade i → cellCenter (1/N) z ∈
        SamplingGeometry.lengthCarrier (F.tube i) (lengths i) (geom.width*(1/N))) →
      F.Separated (geom.separation*(1/N)) → F.Bounded geom.radius →
      (∀ i, c₀*lam/(1/N) ≤ ((F.shade i).card:ℝ)) →
      (∀ i, ((F.shade i).card:ℝ) ≤ C₀*lam/(1/N)) →
      F.FullTwoEnds (1/N) (B₀*(Real.log (2*N))^b) alpha →
      c*N^((33:ℝ)/8-eps)*lam^((15:ℝ)/4)*((M:ℝ)/N^5) ≤ (F.unionCells.card:ℝ) := by
  obtain ⟨c,hc,hestimate⟩ := cap_free geom lengthUpper c₀ C₀ B₀ alpha b eps
    hc₀ hC₀ hB₀ ha hb heps
  refine ⟨c,hc,?_⟩
  intro M F lengths N lam hN hlam hlam1 hlength hadm hsep hbounded hlo hhi hends
  have hN0 : 0 < N := zero_lt_one.trans_le hN
  have hδ : 0 < 1/N := one_div_pos.mpr hN0
  have hδ1 : 1/N ≤ 1 := (div_le_one hN0).mpr hN
  have hlog : Real.log (2/(1/N)) = Real.log (2*N) := by
    congr 1
    field_simp
  have hends' : F.FullTwoEnds (1/N) (B₀*(Real.log (2/(1/N)))^b) alpha := by
    rw [hlog]
    exact hends
  have hbound := hestimate F lengths hδ hδ1 hlam hlam1 hlength hadm hsep hbounded hlo hhi hends'
  have hpower : (1/N)^((7:ℝ)/8+eps) = N^((33:ℝ)/8-eps)/N^5 := by
    rw [one_div,Real.inv_rpow hN0.le,← Real.rpow_neg hN0.le,
      ← Real.rpow_natCast N 5,← Real.rpow_sub hN0]
    congr 1
    ring
  calc
    _ = c*(1/N)^((7:ℝ)/8+eps)*lam^((15:ℝ)/4)*(M:ℝ) := by rw [hpower]; ring
    _ ≤ _ := hbound

end
end KakeyaFormal.SixDimensionalLogarithmicLengths
