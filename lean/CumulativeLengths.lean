import UnmarkedLengthEstimates
import CumulativeEstimate

/-! Cumulative estimates on actual original bounded-length axes. A single
common dilation preserves every integer row and the exact union, including
unequal and empty rows and arbitrarily small cumulative density. -/
namespace KakeyaFormal.CumulativeLengths
open MarkedLengthNormalization UnmarkedLengthEstimates
open scoped BigOperators
noncomputable section

theorem from_cumulative {n : ℕ} {m d p : ℝ}
    (hestimate : CumulativeEstimate n m d p) (hm : 0 ≤ m)
    (geom : Normalization) (lengthUpper eps : ℝ) (heps : 0 < eps) :
    ∃ c : ℝ, 0 < c ∧ ∀ {M : ℕ} (F : TubeFamily n M) (lengths : Fin M → ℝ)
      {δ s A : ℝ},
      0 < δ → δ ≤ 1 → 0 ≤ s → 1 ≤ A →
      (∀ i, lengths i ≤ lengthUpper) →
      (∀ i z, z∈F.shade i → cellCenter δ z ∈
        SamplingGeometry.lengthCarrier (F.tube i) (lengths i) (geom.width*δ)) →
      F.Separated (geom.separation*δ) → F.Bounded geom.radius → F.CapBound δ m A →
      s*(M:ℝ) ≤ δ*∑ i, ((F.shade i).card:ℝ) →
      c*A⁻¹*δ^(m-d+eps)*s^p*(M:ℝ) ≤ (F.unionCells.card:ℝ) := by
  let W := dilation lengthUpper
  have hW : 1 ≤ W := dilation_ge_one _
  have hW0 : 0 < W := dilation_pos _
  obtain ⟨c,hc,hbound⟩ := hestimate (geometry geom lengthUpper) eps heps
  refine ⟨c*factor lengthUpper (m-d+eps) p,mul_pos hc (factor_pos _ _ _),?_⟩
  intro M F lengths δ s A hδ hδ1 hs hA hlength hadm hsep hbase hcap hinc
  have hcum : (s/W)*(M:ℝ) ≤ (δ/W)*∑ i, ((F.shade i).card:ℝ) := by
    have hh := div_le_div_of_nonneg_right hinc hW0.le
    calc
      (s/W)*(M:ℝ) = (s*(M:ℝ))/W := by ring
      _ ≤ (δ*∑ i, ((F.shade i).card:ℝ))/W := hh
      _ = _ := by ring
  let G : CumulativeConfiguration n (geometry geom lengthUpper) m := {
    M := M, δ := δ/W, s := s/W, A := A, family := normalizedFamily F W
    scale_pos := div_pos hδ hW0
    scale_le_one := (div_le_one hW0).mpr (hδ1.trans hW)
    density_nonneg := div_nonneg hs hW0.le
    cap_ge_one := hA
    admissible := admissible F lengths hW0 (fun i => (hlength i).trans (le_max_right _ _)) hadm
    separated := separated F hW hδ.le geom.separation_pos.le hsep
    bounded := bounded F hW0 hbase
    cap_bound := cap_bound F hW hδ hδ1 hm (zero_le_one.trans hA) hcap
    cumulative := hcum }
  have hh := hbound G
  change c*A⁻¹*(δ/W)^(m-d+eps)*(s/W)^p*(M:ℝ) ≤ (F.unionCells.card:ℝ) at hh
  have hid := power_identity (U:=m-d+eps) (p:=p) hδ.le hs hW0.le
  calc
    _ = (c*A⁻¹)*(((W⁻¹)^(m-d+eps)*(W⁻¹)^p)*(δ^(m-d+eps)*s^p))*(M:ℝ) := by
      unfold factor
      ring
    _ = c*A⁻¹*(δ/W)^(m-d+eps)*(s/W)^p*(M:ℝ) := by rw [← hid]; ring
    _ ≤ _ := hh

end
end KakeyaFormal.CumulativeLengths
