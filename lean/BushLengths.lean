import Bush
import UnmarkedLengthEstimates

/-! Exact error-free cumulative bush estimate on original bounded-length
axes. No separation, bounded-position, two-ends or individual density premise
is added, and zero cumulative density and empty populations are included. -/
namespace KakeyaFormal.BushLengths
open MarkedLengthNormalization UnmarkedLengthEstimates
noncomputable section

theorem cumulative (k : ℕ) (width lengthUpper m : ℝ) (hm : 0 < m) :
    ∃ c : ℝ, 0 < c ∧ ∀ {M : ℕ} (F : TubeFamily (k+1) M) (lengths : Fin M → ℝ)
      {δ s A : ℝ},
      0 < δ → δ ≤ 1 → 0 ≤ s → s ≤ 1 → 1 ≤ A →
      (∀ i, lengths i ≤ lengthUpper) →
      (∀ i z, z∈F.shade i → cellCenter δ z ∈
        SamplingGeometry.lengthCarrier (F.tube i) (lengths i) (width*δ)) →
      F.CapBound δ m A → (s/δ)*(M:ℝ) ≤ Bush.incidenceMass F Finset.univ →
      c*A⁻¹*δ^(m/2-1)*s^((m+2)/2)*(M:ℝ) ≤ (F.unionCells.card:ℝ) := by
  let W := dilation lengthUpper
  have hW : 1 ≤ W := dilation_ge_one _
  have hW0 : 0 < W := dilation_pos _
  have hd : 0 < (m+2)/2 := by linarith
  obtain ⟨c,hc,hbound⟩ := Bush.cumulative_bush_estimate k width m hm
  refine ⟨c*factor lengthUpper (m/2-1) ((m+2)/2),mul_pos hc (factor_pos _ _ _),?_⟩
  intro M F lengths δ s A hδ hδ1 hs hs1 hA hlength hadm hcap hmass
  by_cases hspos : 0 < s
  · by_cases hM : 0 < M
    · have hnormmass : ((s/W)/(δ/W))*(M:ℝ) ≤
          Bush.incidenceMass (normalizedFamily F W) Finset.univ := by
        have he : (s/W)/(δ/W)=s/δ := by field_simp
        simpa only [he,Bush.incidenceMass,normalizedFamily] using hmass
      have hh := hbound M (normalizedFamily F W) (δ/W) (s/W) A
        (admissible F lengths hW0 (fun i => (hlength i).trans (le_max_right _ _)) hadm)
        (cap_bound F hW hδ hδ1 hm.le (zero_le_one.trans hA) hcap)
        (div_pos hδ hW0) ((div_le_one hW0).mpr (hδ1.trans hW))
        (div_pos hspos hW0) ((div_le_one hW0).mpr (hs1.trans hW)) hA hM hnormmass
      change c*A⁻¹*(δ/W)^(m/2-1)*(s/W)^((m+2)/2)*(M:ℝ) ≤ (F.unionCells.card:ℝ) at hh
      have hid := power_identity (U:=m/2-1) (p:=(m+2)/2) hδ.le hs hW0.le
      calc
        _ = (c*A⁻¹)*(((W⁻¹)^(m/2-1)*(W⁻¹)^((m+2)/2))*(δ^(m/2-1)*s^((m+2)/2)))*(M:ℝ) := by
          unfold factor
          ring
        _ = c*A⁻¹*(δ/W)^(m/2-1)*(s/W)^((m+2)/2)*(M:ℝ) := by rw [← hid]; ring
        _ ≤ _ := hh
    · have hz : M=0 := Nat.eq_zero_of_not_pos hM
      simp only [hz,Nat.cast_zero,mul_zero]
      exact Nat.cast_nonneg _
  · have hz : s=0 := le_antisymm (le_of_not_gt hspos) hs
    rw [hz,Real.zero_rpow hd.ne',mul_zero,zero_mul]
    exact Nat.cast_nonneg _

end
end KakeyaFormal.BushLengths
