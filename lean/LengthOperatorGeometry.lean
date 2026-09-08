import DilationIntegral

/-! Exact variable-length tube averages, genuine common-dilation domination,
and measurability of the full length-and-position supremum. -/
namespace KakeyaFormal.LengthOperatorGeometry
open MeasureTheory Set SamplingGeometry WidthNormalization MeasurableRescaling Rescaling
open KakeyaOperator
open scoped ENNReal
noncomputable section

def average {n : ℕ} (δ width length : ℝ) (f : Space n → ℝ≥0∞)
    (b : Space n) (v : Direction n) : ℝ≥0∞ :=
  (∫⁻ x in lengthCarrier (tube v b) length (width*δ), f x ∂volume) /
    (volume : Measure (Space n)) (lengthCarrier (tube v b) length (width*δ))

def maximal {n : ℕ} (lower upper width δ : ℝ) (f : Space n → ℝ≥0∞)
    (v : Direction n) : ℝ≥0∞ :=
  ⨆ length : ↥(Icc lower upper), ⨆ b : Space n, average δ width length.val f b v

theorem normalized_carrier_eq {n : ℕ} (T : UnitTube n) {length radius : ℝ}
    (hl : 0 < length) :
    normalizedSet length (lengthCarrier T length radius) =
      (normalizedTube T length).carrier (radius/length) := by
  apply Set.Subset.antisymm
  · simpa only [mul_one,mul_one_div] using
      normalized_length_carrier (width:=radius) (δ:=1) T hl le_rfl _ Set.Subset.rfl
  · intro x hx
    rw [normalized_membership hl]
    obtain ⟨t,ht,hd⟩ := hx
    refine ⟨length*t,⟨mul_nonneg hl.le ht.1,?_⟩,?_⟩
    · simpa using mul_le_mul_of_nonneg_left ht.2 hl.le
    · have ha : rescale length 0 (T.axisPoint (length*t)) =
          (normalizedTube T length).axisPoint t := by
        simpa only [WidthNormalization.normalizedTube,zero_add] using rescale_axisPoint T hl.ne' (0:Space n) 0 t
      rw [← ha,← rescale_inverse hl.ne' (0:Space n) x,rescale_distance hl] at hd
      exact (div_le_div_iff_of_pos_right hl).mp hd

theorem normalized_set_integral {n : ℕ} {W : ℝ} (hW : 0 < W)
    (f : Space n → ℝ≥0∞) (S : Set (Space n)) :
    (∫⁻ x in normalizedSet W S, f (W • x) ∂volume) =
      ENNReal.ofReal ((W^n)⁻¹)*(∫⁻ x in S, f x ∂volume) := by
  rw [normalizedSet,image_eq_preimage hW.ne']
  have he : inverse W (0:Space n) = fun x => W • x := by
    funext x
    simp [MeasurableRescaling.inverse]
  rw [he]
  exact DilationIntegral.set_lintegral_comp hW f S

theorem normalized_measure {n : ℕ} {W : ℝ} (hW : 0 < W) (S : Set (Space n)) :
    (volume : Measure (Space n)) (normalizedSet W S) =
      ENNReal.ofReal ((W^n)⁻¹)*(volume : Measure (Space n)) S := by
  rw [normalizedSet,image_eq_preimage hW.ne']
  have he : inverse W (0:Space n) = fun x => W • x := by
    funext x
    simp [MeasurableRescaling.inverse]
  rw [he]
  change (volume : Measure (Space n)) ((fun x : Space n => W • x) ⁻¹' S) = _
  rw [Measure.addHaar_preimage_smul volume hW.ne']
  simp only [finrank_euclideanSpace,Fintype.card_fin,abs_of_pos (inv_pos.mpr (pow_pos hW n))]

theorem average_eq_unit {n : ℕ} {length : ℝ} (hl : 0 < length)
    (δ width : ℝ) (f : Space n → ℝ≥0∞) (b : Space n) (v : Direction n) :
    average δ width length f b v =
      KakeyaOperator.average (width*δ/length) (fun x => f (length • x)) (length⁻¹ • b) v := by
  have hi := normalized_set_integral hl f (lengthCarrier (tube v b) length (width*δ))
  have hm := normalized_measure hl (lengthCarrier (tube v b) length (width*δ))
  rw [normalized_carrier_eq _ hl] at hi hm
  have ht : normalizedTube (tube v b) length = tube v (length⁻¹ • b) := by
    simp [WidthNormalization.normalizedTube,Rescaling.tube,Rescaling.rescale,KakeyaOperator.tube,UnitTube.axisPoint]
  rw [ht] at hi hm
  unfold average KakeyaOperator.average
  rw [hi,hm]
  exact (ENNReal.mul_div_mul_left _ _ (by positivity) ENNReal.ofReal_ne_top).symm

theorem maximal_ae_congr {n : ℕ} (l u width δ : ℝ)
    {f g : Space n → ℝ≥0∞} (hfg : f =ᵐ[(volume : Measure (Space n))] g) :
    maximal l u width δ f = maximal l u width δ g := by
  funext v
  unfold maximal average
  congr 1
  funext length
  congr 1
  funext b
  rw [lintegral_congr_ae (ae_restrict_of_ae hfg)]

theorem maximal_lowerSemicontinuous {k : ℕ} {l u width δ : ℝ}
    (hl : 0 < l) (hw : 0 < width) (hδ : 0 < δ)
    (f : Space (k+1) → ℝ≥0∞) (hf : Measurable f) :
    LowerSemicontinuous (maximal l u width δ f) := by
  unfold maximal
  apply lowerSemicontinuous_iSup
  intro length
  have hlength : 0 < length.val := hl.trans_le length.property.1
  apply lowerSemicontinuous_iSup
  intro b
  have hg : Measurable (fun x : Space (k+1) => f (length.val • x)) :=
    hf.comp (by fun_prop : Measurable (fun x : Space (k+1) => length.val • x))
  have hp : 0 < width*δ/length.val := div_pos (mul_pos hw hδ) hlength
  have hc : Continuous (fun v : Direction (k+1) => (length.val⁻¹ • b,v)) := by fun_prop
  have hh := (KakeyaOperatorMeasurability.average_lowerSemicontinuous hp _ hg).comp hc
  simpa only [← average_eq_unit hlength,Function.comp_def] using hh

theorem maximal_measurable {k : ℕ} {l u width δ : ℝ}
    (hl : 0 < l) (hw : 0 < width) (hδ : 0 < δ)
    (f : Space (k+1) → ℝ≥0∞) (hf : AEMeasurable f volume) :
    Measurable (maximal l u width δ f) := by
  rw [maximal_ae_congr l u width δ hf.ae_eq_mk]
  exact (maximal_lowerSemicontinuous hl hw hδ _ hf.measurable_mk).measurable

end
end KakeyaFormal.LengthOperatorGeometry
