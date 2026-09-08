import MeasurableLengthEstimates
import MainOperator

/-! Exact Lebesgue integral and eLpNorm scaling under a genuine common
positive homothety. No input measurability or finite-integral premise is
needed for the embedding identities; null-set transport is proved too. -/
namespace KakeyaFormal.DilationIntegral
open MeasureTheory Set
open scoped ENNReal
noncomputable section

def equiv {n : ℕ} {W : ℝ} (hW : 0 < W) : Space n ≃ᵐ Space n where
  toFun x := W • x
  invFun x := W⁻¹ • x
  left_inv x := by simp [smul_smul,hW.ne']
  right_inv x := by simp [smul_smul,hW.ne']
  measurable_toFun := (by fun_prop : Continuous (fun x : Space n => W • x)).measurable
  measurable_invFun := (by fun_prop : Continuous (fun x : Space n => W⁻¹ • x)).measurable

theorem map_volume {n : ℕ} {W : ℝ} (hW : 0 < W) :
    Measure.map (equiv (n:=n) hW) volume = ENNReal.ofReal ((W^n)⁻¹) • volume := by
  ext S hS
  rw [Measure.map_apply (equiv hW).measurable hS]
  change (volume : Measure (Space n)) ((fun x : Space n => W • x) ⁻¹' S) = _
  rw [Measure.addHaar_preimage_smul volume hW.ne']
  simp only [finrank_euclideanSpace,Fintype.card_fin,abs_of_pos (inv_pos.mpr (pow_pos hW n)),
    Measure.smul_apply,smul_eq_mul]

theorem quasiMeasurePreserving {n : ℕ} {W : ℝ} (hW : 0 < W) :
    Measure.QuasiMeasurePreserving (equiv (n:=n) hW) volume volume := by
  refine ⟨(equiv hW).measurable,?_⟩
  rw [map_volume hW]
  exact Measure.smul_absolutelyContinuous

theorem aemeasurable_comp {n : ℕ} {X : Type*} [MeasurableSpace X]
    {W : ℝ} (hW : 0 < W) {f : Space n → X} (hf : AEMeasurable f volume) :
    AEMeasurable (fun x => f (W • x)) volume :=
  hf.comp_quasiMeasurePreserving (quasiMeasurePreserving hW)

theorem lintegral_comp {n : ℕ} {W : ℝ} (hW : 0 < W) (f : Space n → ℝ≥0∞) :
    (∫⁻ x, f (W • x) ∂volume) = ENNReal.ofReal ((W^n)⁻¹)*(∫⁻ x, f x ∂volume) := by
  change (∫⁻ x, f ((equiv hW) x) ∂volume) = _
  rw [← (equiv (n:=n) hW).measurableEmbedding.lintegral_map,map_volume hW,lintegral_smul_measure]
  rfl

theorem set_lintegral_comp {n : ℕ} {W : ℝ} (hW : 0 < W)
    (f : Space n → ℝ≥0∞) (S : Set (Space n)) :
    (∫⁻ x in (fun x : Space n => W • x) ⁻¹' S, f (W • x) ∂volume) =
      ENNReal.ofReal ((W^n)⁻¹)*(∫⁻ x in S, f x ∂volume) := by
  change (∫⁻ x in (equiv hW) ⁻¹' S, f ((equiv hW) x) ∂volume) = _
  rw [← (equiv (n:=n) hW).measurableEmbedding.lintegral_map,
    ← (equiv hW).measurableEmbedding.restrict_map,map_volume hW,
    Measure.restrict_smul,lintegral_smul_measure]
  rfl

theorem norm_comp {n : ℕ} {X : Type*} [TopologicalSpace X] [ContinuousENorm X]
    {W a : ℝ} (hW : 0 < W) (ha : 0 < a) (f : Space n → X) :
    eLpNorm (fun x => f (W • x)) (ENNReal.ofReal a) volume =
      ENNReal.ofReal (W^(-(n:ℝ)/a))*eLpNorm f (ENNReal.ofReal a) volume := by
  change eLpNorm (f ∘ (equiv hW)) (ENNReal.ofReal a) volume = _
  rw [← (equiv (n:=n) hW).measurableEmbedding.eLpNorm_map_measure,map_volume hW,
    eLpNorm_smul_measure_of_ne_top ENNReal.ofReal_ne_top]
  simp only [ENNReal.toReal_div,ENNReal.toReal_one,ENNReal.toReal_ofReal ha.le,smul_eq_mul]
  rw [ENNReal.ofReal_rpow_of_pos (inv_pos.mpr (pow_pos hW n))]
  congr 2
  rw [Real.inv_rpow (pow_nonneg hW.le n),← Real.rpow_natCast_mul hW.le]
  rw [← Real.rpow_neg hW.le]
  congr 1
  ring

end
end KakeyaFormal.DilationIntegral
