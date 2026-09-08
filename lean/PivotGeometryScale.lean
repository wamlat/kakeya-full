import PivotKappaScale
import LegalOutputDirections
import SelectedLiftWitness

/-! One fixed twentieth-power cutoff supplies all numerical perturbation room
used by the actual original-output and normalized-lift constructions. -/
namespace KakeyaFormal.PivotGeometryScale
noncomputable section

def geometryConstant (n : ℕ) (width : ℝ) : ℝ :=
  max 1 (max (12*width)
    (max (4*LegalOutputDirections.roundingConstant n width*(1+2*width))
      (8*SelectedLiftWitness.errorConstant n (2*width))))

theorem constant_bounds (n : ℕ) (width : ℝ) :
    1 ≤ geometryConstant n width ∧ 12*width ≤ geometryConstant n width ∧
      4*LegalOutputDirections.roundingConstant n width*(1+2*width) ≤ geometryConstant n width ∧
      8*SelectedLiftWitness.errorConstant n (2*width) ≤ geometryConstant n width := by
  unfold geometryConstant
  exact ⟨le_max_left _ _,(le_max_left _ _).trans (le_max_right _ _),
    (le_max_left _ _).trans ((le_max_right _ _).trans (le_max_right _ _)),
    (le_max_right _ _).trans ((le_max_right _ _).trans (le_max_right _ _))⟩

/-- Every scalar condition needed after the common legal-sample homothety.
The original mesh and normalized mesh are deliberately kept distinct. -/
structure Tests (n : ℕ) (δ kappa width : ℝ) : Prop where
  original_scale_le_one : δ ≤ 1
  normalized_scale_pos : 0 < δ/(1+2*width)
  normalized_scale_le_one : δ/(1+2*width) ≤ 1
  normalized_kappa_pos : 0 < kappa/(1+2*width)
  normalized_kappa_le_one : kappa/(1+2*width) ≤ 1
  original_scale_le_normalized_kappa : δ ≤ kappa/(1+2*width)
  collision_small : (6*width/kappa)*δ ≤ 1/2
  original_output_noncollapse : 4*LegalOutputDirections.roundingConstant n width*(1+2*width)*δ ≤ kappa^2
  selected_slab_small : (n:ℝ)*(δ/(1+2*width)) ≤ (kappa/(1+2*width))^5/4
  attached_witness_small : 2*SelectedLiftWitness.errorConstant n (2*width)*(δ/(1+2*width)) ≤
    (kappa/(1+2*width))^5/4

theorem tests_of_normalized_twentieth (n : ℕ) {δ kappa width : ℝ}
    (hδ : 0 < δ) (hk : 0 < kappa) (hk1 : kappa ≤ 1) (hw : 0 ≤ width)
    (hscale : geometryConstant n width ≤ (1/δ)*(kappa/(1+2*width))^20) :
    Tests n δ kappa width := by
  let R := 1+2*width
  let kap := kappa/R
  let C := SelectedLiftWitness.errorConstant n (2*width)
  have hR1 : 1 ≤ R := by dsimp [R]; linarith
  have hR : 0 < R := zero_lt_one.trans_le hR1
  have hkap : 0 < kap := div_pos hk hR
  have hkapk : kap ≤ kappa := div_le_self hk.le hR1
  have hkap1 : kap ≤ 1 := hkapk.trans hk1
  have hδnorm : δ/R ≤ δ := div_le_self hδ.le hR1
  have hC : 0 ≤ C := SelectedLiftWitness.errorConstant_nonneg n (by positivity)
  have hCn : (n:ℝ) ≤ 2*C := by dsimp [C,SelectedLiftWitness.errorConstant]; linarith
  obtain ⟨hT1,hT12,hT4,hT8⟩ := constant_bounds n width
  have hbudget : geometryConstant n width*δ ≤ kap^20 := by
    apply (le_div_iff₀ hδ).mp
    convert hscale using 1 <;> first | rfl | ring
  have hpow1 : kap^20 ≤ kap := by
    simpa only [pow_one] using pow_le_pow_of_le_one hkap.le hkap1 (show 1 ≤ (20:ℕ) by omega)
  have hpow2 : kap^20 ≤ kap^2 := pow_le_pow_of_le_one hkap.le hkap1 (by omega : 2 ≤ (20:ℕ))
  have hpow5 : kap^20 ≤ kap^5 := pow_le_pow_of_le_one hkap.le hkap1 (by omega : 5 ≤ (20:ℕ))
  have hTδ : δ ≤ geometryConstant n width*δ := by
    simpa only [one_mul] using mul_le_mul_of_nonneg_right hT1 hδ.le
  have hδkap : δ ≤ kap := hTδ.trans (hbudget.trans hpow1)
  have hcoll : (6*width/kappa)*δ ≤ 1/2 := by
    have hh := (mul_le_mul_of_nonneg_right hT12 hδ.le).trans (hbudget.trans (hpow1.trans hkapk))
    rw [show (6*width/kappa)*δ = (6*width*δ)/kappa by ring]
    exact (div_le_iff₀ hk).mpr (by nlinarith)
  have hnoncollapse : 4*LegalOutputDirections.roundingConstant n width*(1+2*width)*δ ≤ kappa^2 :=
    (mul_le_mul_of_nonneg_right hT4 hδ.le).trans
      (hbudget.trans (hpow2.trans (pow_le_pow_left₀ hkap.le hkapk 2)))
  have herror : 2*C*(δ/R) ≤ kap^5/4 := by
    have hh := (mul_le_mul_of_nonneg_left hδnorm (by positivity : 0 ≤ 8*C)).trans
      ((mul_le_mul_of_nonneg_right hT8 hδ.le).trans (hbudget.trans hpow5))
    nlinarith
  exact ⟨hδkap.trans hkap1,div_pos hδ hR,hδnorm.trans (hδkap.trans hkap1),hkap,hkap1,hδkap,
    hcoll,hnoncollapse,(mul_le_mul_of_nonneg_right hCn (div_pos hδ hR).le).trans herror,herror⟩

/-- The manuscript's original N*kappa^20 cutoff differs by only a fixed
normalization factor R^20 from the normalized cutoff above. -/
theorem tests_of_original_twentieth (n : ℕ) {δ kappa width : ℝ}
    (hδ : 0 < δ) (hk : 0 < kappa) (hk1 : kappa ≤ 1) (hw : 0 ≤ width)
    (hscale : geometryConstant n width*(1+2*width)^20 ≤ (1/δ)*kappa^20) :
    Tests n δ kappa width := by
  apply tests_of_normalized_twentieth n hδ hk hk1 hw
  have hR : 0 < 1+2*width := by positivity
  have hh := (le_div_iff₀ (pow_pos hR 20)).mpr hscale
  rw [div_pow]
  exact hh.trans_eq (by ring)

/-- A single positive threshold, fixed before the concentration coefficients
or configuration, supplies all geometric tests for the explicit pivot choice.
The allowed growth of the later coefficients is stated quantitatively. -/
theorem uniform_choice_tests (n : ℕ) {width B₀ K₀ alpha beta b q : ℝ}
    (hw : 0 ≤ width) (hB₀ : 0 < B₀) (hK₀ : 0 < K₀)
    (ha : 0 < alpha) (hb : 0 < beta) (hb₀ : 0 ≤ b) (hq : 0 ≤ q) :
    ∃ δ₀ : ℝ, 0 < δ₀ ∧ δ₀ ≤ 1 ∧ ∀ δ B K : ℝ, 0 < δ → δ ≤ δ₀ →
      1 ≤ B → 1 ≤ K →
      B ≤ B₀*(Real.log (2/δ))^b → K ≤ K₀*(Real.log (2/δ))^q →
      Tests n δ (PivotKappa.choice width B K alpha beta) width := by
  obtain ⟨δ₀,hδ₀,hδ₀1,hcut⟩ := PivotKappaScale.normalized_choice_small_scales
    (R:=1+2*width) (T:=geometryConstant n width)
    hw hB₀ hK₀ ha hb hb₀ hq (by positivity)
  refine ⟨δ₀,hδ₀,hδ₀1,?_⟩
  intro δ B K hδ hsmall hB hK hBB hKK
  have hBp : 0 < B := zero_lt_one.trans_le hB
  have hKp : 0 < K := zero_lt_one.trans_le hK
  have hk := PivotKappa.choice_pos (alpha:=alpha) (beta:=beta) hw hBp hKp
  have hk1 : PivotKappa.choice width B K alpha beta ≤ 1 :=
    (PivotKappa.choice_le_hundredth hw hB hK ha hb).trans (by norm_num)
  exact tests_of_normalized_twentieth n hδ hk hk1 hw
    (hcut δ B K hδ hsmall hBp hKp hBB hKK).2

end
end KakeyaFormal.PivotGeometryScale
