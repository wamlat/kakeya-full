import CumulativeEstimate

/-! Per-tube lower density needs no Jensen inequality. Actual simultaneous
integer trimming and fixed geometric normalization suffice for every p>0. -/
namespace KakeyaFormal.LowerDensityEstimate
open Finset DiscreteMeasurable
open scoped BigOperators
noncomputable section
open Classical

/-- Apply the original estimate after trimming every tube to ceil(s/delta)
actual cells. The constant precedes scale, density, population and cap factor;
no logarithmic loss or cumulative concavity assumption is used. -/
theorem lower_density {k : ℕ} {m d p : ℝ}
    (hbase : DiscreteEstimate k m d p) (hp : 0 < p)
    (geom : Normalization) (eps : ℝ) (heps : 0 < eps) :
    ∃ c : ℝ, 0 < c ∧ ∀ F : CumulativeConfiguration k geom m,
      (∀ i, F.s ≤ F.δ*((F.family.shade i).card : ℝ)) →
      c*F.A⁻¹*F.δ^(m-d+eps)*F.s^p*F.M ≤ (F.family.unionCells.card : ℝ) := by
  obtain ⟨c,hc,hestimate⟩ := hbase geom eps heps
  let C := gridCountConstant k geom.width
  have hC : 0 < C := zero_lt_one.trans_le (gridCountConstant_ge_one _ _)
  refine ⟨c/(2*C)^p,by positivity,?_⟩
  intro F hdense
  by_cases hM : F.M=0
  · simp only [hM,Nat.cast_zero,mul_zero]
    positivity
  by_cases hs : F.s=0
  · rw [hs,Real.zero_rpow hp.ne']
    simp only [mul_zero,zero_mul]
    positivity
  have hs0 : 0 < F.s := lt_of_le_of_ne F.density_nonneg (Ne.symm hs)
  have hM0 : 0 < F.M := Nat.pos_of_ne_zero hM
  let K := Nat.ceil (F.s/F.δ)
  have hK : 0 < K := Nat.ceil_pos.mpr (div_pos hs0 F.scale_pos)
  have hcards (i : Fin F.M) (_ : i ∈ (univ : Finset (Fin F.M))) :
      K ≤ (F.family.shade i).card := by
    apply Nat.ceil_le.mpr
    exact (div_le_iff₀ F.scale_pos).mpr (by simpa only [mul_comm] using hdense i)
  have hS : (univ : Finset (Fin F.M)).Nonempty := ⟨⟨0,hM0⟩,mem_univ _⟩
  have hbound := Cumulative.subfamily_bound hc hp.le hestimate F univ hS hK hcards
  simp only [card_univ,Fintype.card_fin] at hbound
  have hceil : F.s ≤ F.δ*(K : ℝ) := by
    have hh := Nat.le_ceil (F.s/F.δ)
    exact (div_le_iff₀ F.scale_pos).mp hh |>.trans_eq (mul_comm _ _)
  have hpow : (F.s/(2*C))^p ≤ (F.δ*(K:ℝ)/(2*C))^p :=
    Real.rpow_le_rpow (by positivity) (div_le_div_of_nonneg_right hceil (by positivity)) hp.le
  have hA0 : 0 < F.A := zero_lt_one.trans_le F.cap_ge_one
  have hmul := mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hpow
    (by positivity [F.scale_pos] : 0 ≤ c*F.A⁻¹*F.δ^(m-d+eps))) (Nat.cast_nonneg F.M)
  calc
    _ = c*F.A⁻¹*F.δ^(m-d+eps)*(F.s/(2*C))^p*F.M := by
      rw [Real.div_rpow F.density_nonneg (by positivity : 0 ≤ 2*C)]
      ring
    _ ≤ c*F.A⁻¹*F.δ^(m-d+eps)*(F.δ*(K:ℝ)/(2*C))^p*F.M := hmul
    _ ≤ _ := hbound

end
end KakeyaFormal.LowerDensityEstimate
