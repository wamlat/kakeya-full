import UnmarkedLengthEstimates
import FractionalSeedFullRange
import ProjectiveGeometry

/-! A cap-free five-dimensional seed on the original bounded-length axes and
original grid shadings. Full cap control is proved from actual direction
separation, and all fixed cap/geometric losses are absorbed into the constant. -/
namespace KakeyaFormal.FiveDimensionalLengthSeed
open ProjectiveGeometry
noncomputable section

/-- The proved unrestricted m=4 seed in actual dimension five. -/
theorem discrete_seed : DiscreteEstimate 5 4 (7/2) (7/2) := by
  have h := FractionalSeedFullRange.fractional_discrete_seed 3 (m:=4) (by norm_num)
  norm_num at h
  exact h

/-- Every original row has only a fixed positive LOWER density assumption.
There is no cap coefficient, two-ends premise, upper density bound or lambda<=1.
All individual axis lengths and original shadings remain the caller's data. -/
theorem original_length_bound (geom : Normalization) (lengthUpper crow eps : ℝ)
    (hcrow : 0 < crow) (heps : 0 < eps) :
    ∃ c : ℝ, 0 < c ∧ ∀ {M : ℕ} (H : TubeFamily 5 M) (lengths : Fin M → ℝ)
      {δ lam : ℝ},
      0 < δ → δ ≤ 1 → 0 < lam →
      (∀ i, lengths i ≤ lengthUpper) →
      (∀ i z, z∈H.shade i → cellCenter δ z ∈
        SamplingGeometry.lengthCarrier (H.tube i) (lengths i) (geom.width*δ)) →
      H.Separated (geom.separation*δ) → H.Bounded geom.radius →
      (∀ i, crow*lam/δ ≤ ((H.shade i).card:ℝ)) →
      c*δ^((1:ℝ)/2+eps)*lam^((7:ℝ)/2)*(M:ℝ) ≤ (H.unionCells.card:ℝ) := by
  let A₀ := fullDirectionCoefficient 4 geom.separation
  have hA₀ : 1 ≤ A₀ := fullDirectionCoefficient_ge_one 4 geom.separation_pos
  have hApos : 0 < A₀ := zero_lt_one.trans_le hA₀
  obtain ⟨c,hc,hbound⟩ := UnmarkedLengthEstimates.from_discrete discrete_seed
    (by norm_num : (0:ℝ) ≤ 4) (by norm_num : (0:ℝ) < 7/2)
    geom lengthUpper crow eps hcrow heps
  refine ⟨c*A₀⁻¹,mul_pos hc (inv_pos.mpr hApos),?_⟩
  intro M H lengths δ lam hδ hδ1 hlam hlength hadm hsep hbase hrow
  have hcap : H.CapBound δ 4 A₀ :=
    separated_tube_family_cap_bound H hδ geom.separation_pos hsep
  have hh := hbound H lengths hδ hδ1 hlam hA₀ hlength hadm hsep hbase hcap hrow
  have he : (4:ℝ)-7/2+eps=1/2+eps := by ring
  simpa only [he] using hh

end
end KakeyaFormal.FiveDimensionalLengthSeed
