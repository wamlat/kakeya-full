import GridMarked

/-! The actual measurable broad hairbrush kernel applied to concrete finite
shadings via exact whole-cell realization and common width normalization. -/
namespace KakeyaFormal.GridHairbrush
open MeasureTheory WidthNormalization GridShadingMeasure GridMarked
open HairbrushKernel HairbrushAllScales HairbrushScales HairbrushSelection
open scoped BigOperators ENNReal
noncomputable section
open Classical

/-- Actual lower and upper finite shading counts give the exact normalized
measurable density interval needed by the broad hairbrush. -/
theorem realized_density {k M : ℕ} (F : TubeFamily (k+2) M) {δ W lam upper : ℝ}
    (hδ : 0 < δ) (hW : 0 < W)
    (hlower : ∀ i, lam ≤ δ*((F.shade i).card:ℝ))
    (hupper : ∀ i, δ*((F.shade i).card:ℝ) ≤ upper) :
    ∀ i, (lam/W^(k+2))*δ^(k+1) ≤ (volume : Measure (Space (k+2))).real (shading F δ W i) ∧
      (volume : Measure (Space (k+2))).real (shading F δ W i) ≤ (upper/W^(k+2))*δ^(k+1) := by
  intro i
  have hlo := mul_le_mul_of_nonneg_left (hlower i) (pow_pos hδ (k+1)).le
  have hhi := mul_le_mul_of_nonneg_left (hupper i) (pow_pos hδ (k+1)).le
  have hpow : δ^(k+2) = δ^(k+1)*δ := pow_succ δ (k+1)
  simp only [shading,grid_mass _ hδ hW]
  have hlo' := div_le_div_of_nonneg_right hlo (pow_pos hW (k+2)).le
  have hhi' := div_le_div_of_nonneg_right hhi (pow_pos hW (k+2)).le
  rw [hpow]
  constructor
  · simpa only [div_eq_mul_inv,mul_assoc,mul_comm,mul_left_comm] using hlo'
  · simpa only [div_eq_mul_inv,mul_assoc,mul_comm,mul_left_comm] using hhi'

/-- A direct finite-grid broad hairbrush inequality. Its inputs are actual
finite marked incidences, center-ball tests and pointwise cap counts. No
measurable realization, volume comparison, multiplicity selection, chosen
radius or analytic hairbrush conclusion is postulated. -/
theorem finite_broad_hairbrush {k M : ℕ} (F : TubeFamily (k+2) M) (H : Finset (Cell (k+2)))
    {δ width lam upper B alpha beta K tau m A : ℝ}
    (hM : 0 < M) (hδ : 0 < δ) (hδ1 : δ ≤ 1)
    (hlam : 0 ≤ lam) (hlam1 : lam ≤ 1) (hlamu : lam ≤ upper) (hu : 0 < upper)
    (hB : 1 ≤ B) (ha : 0 < alpha) (hK : 1 ≤ K) (hb : 0 < beta)
    (htau : 0 < tau) (htau1 : tau ≤ 1) (hm : 1 ≤ m) (hA : 1 ≤ A)
    (hadm : F.Admissible width δ) (hsep : F.Separated δ) (hcap : F.CapBound δ m A)
    (hlower : ∀ i, lam ≤ δ*((F.shade i).card:ℝ))
    (hupper : ∀ i, δ*((F.shade i).card:ℝ) ≤ upper)
    (hhalf : (∑ i, ((F.shade i).card:ℝ))/2 ≤ ∑ i, ((F.shade i ∩ H).card:ℝ))
    (hbroad : ∀ q ∈ H,
      AngularDecomposition.Broad F (Finset.univ.filter (fun i => q ∈ F.shade i)) δ beta tau K)
    (hends : ∀ i, ∀ x : Space (k+2), ∀ r : ℝ, δ ≤ r → r ≤ 1 →
      (((F.shade i).filter (fun q => dist (cellCenter δ q) x ≤ r)).card:ℝ) ≤
        B*r^alpha*((F.shade i).card:ℝ)) :
    let W := widthFactor (k+2) width
    let B' := B*(1+((k+2:ℕ):ℝ)/2)^alpha*W^alpha
    let K' := K*tau^(-beta)
    (concentrationRadius B' alpha*concentrationRadius K' beta)^(k+1)*
        (∑ i, ((F.shade i ∩ H).card:ℝ))*(lam/W^(k+2))^((3:ℝ)/2)*δ^((m-1)/2)/
      (allScaleConstant k*Real.sqrt (A*(upper/W^(k+2)))*(hairbrushLog k δ)^((5:ℝ)/2)) ≤
        (F.unionCells.card:ℝ) := by
  let W := widthFactor (k+2) width
  let B' := B*(1+((k+2:ℕ):ℝ)/2)^alpha*W^alpha
  let K' := K*tau^(-beta)
  have hW1 : 1 ≤ W := widthFactor_ge_one _ _
  have hW : 0 < W := widthFactor_pos _ _
  have hWpow : 1 ≤ W^(k+2) := one_le_pow₀ hW1
  have hB' : 1 ≤ B' := by
    have hc : 1 ≤ (1+((k+2:ℕ):ℝ)/2)^alpha := Real.one_le_rpow (by have hk : (0:ℝ) ≤ (k+2:ℕ) := Nat.cast_nonneg _; linarith) ha.le
    have hw := Real.one_le_rpow hW1 ha.le
    dsimp [B']
    have hbc : 1 ≤ B*(1+((k+2:ℕ):ℝ)/2)^alpha := by nlinarith
    calc
      1 ≤ W^alpha := hw
      _ ≤ B*(1+((k+2:ℕ):ℝ)/2)^alpha*W^alpha := by
        simpa only [one_mul] using mul_le_mul_of_nonneg_right hbc (Real.rpow_nonneg hW.le alpha)
  have hK' : 1 ≤ K' := by
    have ht := Real.one_le_rpow_of_pos_of_le_one_of_nonpos htau htau1 (by linarith : -beta ≤ 0)
    dsimp [K']
    nlinarith
  have hdens := realized_density F hδ hW hlower hupper
  have hends' := shading_two_ends F hδ hW1 hB ha.le hends
  have hcore := chosen_radius_hairbrush (family F W) (shading F δ W) (marked H δ W)
    hM hδ hδ1 hB' ha hK' hb (div_nonneg hlam (pow_pos hW (k+2)).le)
    ((div_le_one (pow_pos hW (k+2))).mpr (hlam1.trans hWpow))
    (div_le_div_of_nonneg_right hlamu (pow_pos hW (k+2)).le) hm hA
    (div_pos hu (pow_pos hW (k+2))) (separated F W δ hsep)
    (shading_measurable F hW) (fun i => grid_carrier F hδ hadm i)
    (marked_measurable H hW) (marked_half F H hδ hW hhalf)
    (pointwise_broad F H hδ hW htau hbroad) (fun i => (hdens i).1)
    (fun i x r hr _ => hends' i x r hr) (cap_bound F W δ m A hcap) (fun i => (hdens i).2)
  rw [marked_mass F H hδ hW] at hcore
  change _ ≤ (volume : Measure (Space (k+2))).real (⋃ i, normalizedSet W (cellUnion δ (F.shade i))) at hcore
  rw [grid_union_mass F hδ hW] at hcore
  have hfactor : 0 < δ^(k+2)/W^(k+2) := by positivity
  apply (mul_le_mul_iff_left₀ hfactor).mp
  convert hcore using 1 <;> first | rfl | ring

end
end KakeyaFormal.GridHairbrush
