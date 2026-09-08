import LogarithmicTwoEnds
import TwoEndsPivot

/-! The standalone first-step Lemma6 for ORIGINAL logarithmically growing
two-ends constants. The density exponent is15/4, the set exponent is33/8,
and direction separation supplies the ambient cap bound internally. -/
namespace KakeyaFormal.SixDimensionalLogarithmic
noncomputable section

/-- The real-cap configuration form, with all log-budget parameters fixed
before the original scale, density, family and cap coefficient. -/
theorem configuration_estimate (geom : Normalization) (B₀ alpha b eps : ℝ)
    (hB₀ : 1 ≤ B₀) (ha : 0 < alpha) (hb : 0 ≤ b) (heps : 0 < eps) :
    ∃ c : ℝ, 0 < c ∧ ∀ F : ShadedConfiguration 6 geom 5,
      F.family.FullTwoEnds F.δ (B₀*(Real.log (2/F.δ))^b) alpha →
      c*F.A⁻¹*F.δ^((7:ℝ)/8+eps)*F.lam^((15:ℝ)/4)*F.M ≤
        (F.family.unionCells.card:ℝ) := by
  have h := LogarithmicTwoEnds.estimate (k:=5) TwoEndsPivot.six_dimensional
    (by norm_num) (by norm_num) geom B₀ alpha b eps hB₀ ha hb heps
  norm_num at h
  exact h

/-- No cap premise is required in the source six-dimensional statement.
The original separated directions supply its fixed ambient cap coefficient. -/
theorem cap_free (geom : Normalization) (B₀ alpha b eps : ℝ)
    (hB₀ : 1 ≤ B₀) (ha : 0 < alpha) (hb : 0 ≤ b) (heps : 0 < eps) :
    ∃ c : ℝ, 0 < c ∧ ∀ {M : ℕ} (F : TubeFamily 6 M) {δ lam : ℝ},
      0 < δ → δ ≤ 1 → 0 < lam → lam ≤ 1 →
      F.Admissible geom.width δ → F.Separated (geom.separation*δ) →
      F.Bounded geom.radius → F.Comparable δ lam →
      F.FullTwoEnds δ (B₀*(Real.log (2/δ))^b) alpha →
      c*δ^((7:ℝ)/8+eps)*lam^((15:ℝ)/4)*(M:ℝ) ≤ (F.unionCells.card:ℝ) := by
  let A₀ := ProjectiveGeometry.fullDirectionCoefficient 5 geom.separation
  have hA₀ : 1 ≤ A₀ := ProjectiveGeometry.fullDirectionCoefficient_ge_one 5 geom.separation_pos
  obtain ⟨c,hc,hestimate⟩ := configuration_estimate geom B₀ alpha b eps hB₀ ha hb heps
  refine ⟨c*A₀⁻¹, mul_pos hc (inv_pos.mpr (zero_lt_one.trans_le hA₀)), ?_⟩
  intro M F δ lam hδ hδ1 hlam hlam1 hadm hsep hbounded hcomp hends
  let Q : ShadedConfiguration 6 geom 5 := {
    M := M, δ := δ, lam := lam, A := A₀, family := F,
    scale_pos := hδ, scale_le_one := hδ1,
    density_pos := hlam, density_le_one := hlam1,
    cap_ge_one := hA₀, admissible := hadm, separated := hsep,
    bounded := hbounded, comparable := hcomp,
    cap_bound := by
      simpa only [Nat.cast_ofNat] using
        ProjectiveGeometry.separated_tube_family_cap_bound (k:=5) F hδ geom.separation_pos hsep }
  exact hestimate Q hends

/-- Literal first-step (25): E≥c N^(33/8-eps) lambda^(15/4) S,
where S=M/N^5. The original two-ends coefficient is B0 log(2N)^b,
and the one positive constant is chosen before N,lambda,M and every family. -/
theorem source_notation (geom : Normalization) (B₀ alpha b eps : ℝ)
    (hB₀ : 1 ≤ B₀) (ha : 0 < alpha) (hb : 0 ≤ b) (heps : 0 < eps) :
    ∃ c : ℝ, 0 < c ∧ ∀ {M : ℕ} (F : TubeFamily 6 M) {N lam : ℝ},
      1 ≤ N → 0 < lam → lam ≤ 1 →
      F.Admissible geom.width (1/N) → F.Separated (geom.separation*(1/N)) →
      F.Bounded geom.radius → F.Comparable (1/N) lam →
      F.FullTwoEnds (1/N) (B₀*(Real.log (2*N))^b) alpha →
      c*N^((33:ℝ)/8-eps)*lam^((15:ℝ)/4)*((M:ℝ)/N^5) ≤ (F.unionCells.card:ℝ) := by
  obtain ⟨c,hc,hestimate⟩ := cap_free geom B₀ alpha b eps hB₀ ha hb heps
  refine ⟨c,hc,?_⟩
  intro M F N lam hN hlam hlam1 hadm hsep hbounded hcomp hends
  have hN0 : 0 < N := zero_lt_one.trans_le hN
  have hδ : 0 < 1/N := one_div_pos.mpr hN0
  have hδ1 : 1/N ≤ 1 := (div_le_one hN0).mpr hN
  have hlog : Real.log (2/(1/N)) = Real.log (2*N) := by
    congr 1
    field_simp
  have hends' : F.FullTwoEnds (1/N) (B₀*(Real.log (2/(1/N)))^b) alpha := by
    rw [hlog]
    exact hends
  have hbound := hestimate F hδ hδ1 hlam hlam1 hadm hsep hbounded hcomp hends'
  have hpower : (1/N)^((7:ℝ)/8+eps) = N^((33:ℝ)/8-eps)/N^5 := by
    rw [one_div, Real.inv_rpow hN0.le, ← Real.rpow_neg hN0.le,
      ← Real.rpow_natCast N 5, ← Real.rpow_sub hN0]
    congr 1
    ring
  calc
    _ = c*(1/N)^((7:ℝ)/8+eps)*lam^((15:ℝ)/4)*(M:ℝ) := by
      rw [hpower]
      ring
    _ ≤ _ := hbound

end
end KakeyaFormal.SixDimensionalLogarithmic
