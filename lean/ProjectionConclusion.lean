import FractionalSeedFullRange

/-! The literal cumulative conclusion of Lemma2.1. The proved fractional
seed supplies it directly in ambient seven; this module makes no claim to
construct the manuscript's alternative Gaussian projection proof. -/
namespace KakeyaFormal.ProjectionConclusion
open scoped BigOperators
noncomputable section

/-- Exact scale and cumulative-density exponents of (2.2), including unequal
and empty shadings and arbitrarily small cumulative density. -/
theorem source_cumulative (geom : Normalization) {eps : ℝ} (heps : 0 < eps) :
    ∃ c : ℝ, 0 < c ∧ ∀ F : CumulativeConfiguration 7 geom 4,
      c*F.A⁻¹*F.δ^((1:ℝ)/2+eps)*F.s^((7:ℝ)/2+eps)*(F.M:ℝ) ≤
        (F.family.unionCells.card:ℝ) := by
  have h := FractionalSeedFullRange.source_cumulative 5 (m:=4) (by norm_num) geom heps
  norm_num only [show ((4:ℝ)-3)/2=1/2 by norm_num,
    show ((4:ℝ)+3)/2=7/2 by norm_num] at h
  exact h

/-- Literal N-notation for (2.2), with the original finite family and the
actual total incidence premise s*N*M. The constant precedes N,A,s,M,F. -/
theorem source_count (geom : Normalization) {eps : ℝ} (heps : 0 < eps) :
    ∃ c : ℝ, 0 < c ∧ ∀ M : ℕ, ∀ F : TubeFamily 7 M, ∀ N A s : ℝ,
      1 ≤ N → 1 ≤ A → 0 ≤ s →
      F.Admissible geom.width (1/N) → F.Separated (geom.separation*(1/N)) →
      F.Bounded geom.radius → F.CapBound (1/N) 4 A →
      s*N*(M:ℝ) ≤ ∑ i, ((F.shade i).card:ℝ) →
      c*A⁻¹*N^(-(1:ℝ)/2-eps)*s^((7:ℝ)/2+eps)*(M:ℝ) ≤
        (F.unionCells.card:ℝ) := by
  obtain ⟨c,hc,hbound⟩ := source_cumulative geom heps
  refine ⟨c,hc,?_⟩
  intro M F N A s hN hA hs hadm hsep hbounded hcap hinc
  have hN0 : 0 < N := zero_lt_one.trans_le hN
  have hcum : s*(M:ℝ) ≤ (1/N)*∑ i, ((F.shade i).card:ℝ) := by
    rw [one_div,mul_comm N⁻¹]
    apply (le_div_iff₀ hN0).mpr
    simpa only [mul_assoc,mul_left_comm,mul_comm] using hinc
  let G : CumulativeConfiguration 7 geom 4 :=
    { M:=M, δ:=1/N, s:=s, A:=A, family:=F,
      scale_pos:=one_div_pos.mpr hN0, scale_le_one:=(div_le_one hN0).mpr hN,
      density_nonneg:=hs, cap_ge_one:=hA, admissible:=hadm, separated:=hsep,
      bounded:=hbounded, cap_bound:=hcap, cumulative:=hcum }
  have hh := hbound G
  have hp : (1/N)^((1:ℝ)/2+eps) = N^(-(1:ℝ)/2-eps) := by
    rw [one_div,← Real.rpow_neg_eq_inv_rpow]
    congr 1
    ring
  simpa only [G,hp] using hh

end
end KakeyaFormal.ProjectionConclusion
