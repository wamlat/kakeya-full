import Mathlib.Analysis.SpecialFunctions.Pow.Integral

/-! Power layer cake for actual measurable ENNReal-valued functions, including
infinite values. Monotone finite truncations reduce it to the proved real formula. -/
namespace KakeyaFormal.ENNRealLayerCake
open MeasureTheory Set
open scoped ENNReal
noncomputable section

def truncate {X : Type*} (f : X → ℝ≥0∞) (n : ℕ) (x : X) : ℝ≥0∞ := min (f x) n

theorem truncate_finite {X : Type*} (f : X → ℝ≥0∞) (n : ℕ) (x : X) :
    truncate f n x ≠ ∞ :=
  (lt_of_le_of_lt (min_le_right _ _) (ENNReal.natCast_lt_top n)).ne

theorem truncate_mono {X : Type*} (f : X → ℝ≥0∞) : Monotone (truncate f) :=
  fun _ _ h _ => min_le_min_left _ (by exact_mod_cast h)

theorem truncate_iSup {X : Type*} (f : X → ℝ≥0∞) (x : X) :
    (⨆ n : ℕ, truncate f n x) = f x := by
  change (⨆ n : ℕ, f x ⊓ (n : ℝ≥0∞)) = f x
  rw [← inf_iSup_eq,ENNReal.iSup_natCast,inf_top_eq]

theorem truncate_measurable {X : Type*} [MeasurableSpace X]
    {f : X → ℝ≥0∞} (hf : Measurable f) (n : ℕ) : Measurable (truncate f n) :=
  hf.min measurable_const

theorem tail_measurable {X : Type*} [MeasurableSpace X] (μ : Measure X)
    (f : X → ℝ≥0∞) : Measurable (fun t : ℝ => μ {x | ENNReal.ofReal t < f x}) := by
  apply Antitone.measurable
  intro s t hst
  exact measure_mono (fun _ hx => (ENNReal.ofReal_le_ofReal hst).trans_lt hx)

theorem finite_layercake {X : Type*} [MeasurableSpace X] (μ : Measure X)
    {f : X → ℝ≥0∞} (hf : Measurable f) (hfinite : ∀ x, f x ≠ ∞)
    {p : ℝ} (hp : 0 < p) :
    (∫⁻ x, f x ^ p ∂μ) = ENNReal.ofReal p *
      ∫⁻ t in Ioi (0:ℝ), μ {x | ENNReal.ofReal t < f x} * ENNReal.ofReal (t^(p-1)) := by
  have h := lintegral_rpow_eq_lintegral_meas_lt_mul μ
    (ae_of_all _ (fun x => ENNReal.toReal_nonneg)) hf.ennreal_toReal.aemeasurable hp
  have hlhs : (fun x => ENNReal.ofReal ((f x).toReal ^ p)) = fun x => f x ^ p := by
    funext x
    rw [← ENNReal.ofReal_rpow_of_nonneg ENNReal.toReal_nonneg hp.le,
      ENNReal.ofReal_toReal (hfinite x)]
  rw [hlhs] at h
  rw [h]
  congr 1
  apply setLIntegral_congr_fun measurableSet_Ioi
  intro t ht
  have heq : {x | t < (f x).toReal} = {x | ENNReal.ofReal t < f x} := by
    ext x
    exact (ENNReal.ofReal_lt_iff_lt_toReal ht.le (hfinite x)).symm
  dsimp only
  rw [heq]

/-- Full strict-level power layer cake, with no a.e.-finiteness hypothesis. -/
theorem power_layercake {X : Type*} [MeasurableSpace X] (μ : Measure X)
    {f : X → ℝ≥0∞} (hf : Measurable f) {p : ℝ} (hp : 0 < p) :
    (∫⁻ x, f x ^ p ∂μ) = ENNReal.ofReal p *
      ∫⁻ t in Ioi (0:ℝ), μ {x | ENNReal.ofReal t < f x} * ENNReal.ofReal (t^(p-1)) := by
  have hpow (x : X) : (⨆ n : ℕ, truncate f n x ^ p) = f x ^ p := by
    have h := (ENNReal.orderIsoRpow p hp).map_iSup (fun n => truncate f n x)
    simpa only [ENNReal.orderIsoRpow_apply,truncate_iSup] using h.symm
  have hsets (t : ℝ) : {x | ENNReal.ofReal t < f x} =
      ⋃ n : ℕ, {x | ENNReal.ofReal t < truncate f n x} := by
    ext x
    simp only [mem_ofPred_eq,mem_iUnion]
    rw [← truncate_iSup f x]
    exact lt_iSup_iff
  have hmsets (t : ℝ) : Monotone (fun n : ℕ => {x | ENNReal.ofReal t < truncate f n x}) :=
    fun _ _ h _ hx => hx.trans_le (truncate_mono f h _)
  have htail (t : ℝ) : μ {x | ENNReal.ofReal t < f x} =
      ⨆ n : ℕ, μ {x | ENNReal.ofReal t < truncate f n x} := by
    rw [hsets,(hmsets t).measure_iUnion]
  have hmono : Monotone (fun n : ℕ => fun t : ℝ =>
      μ {x | ENNReal.ofReal t < truncate f n x} * ENNReal.ofReal (t^(p-1))) := by
    intro i j hij t
    exact mul_le_mul' (measure_mono (hmsets t hij)) le_rfl
  have hmeas (n : ℕ) : Measurable (fun t : ℝ =>
      μ {x | ENNReal.ofReal t < truncate f n x} * ENNReal.ofReal (t^(p-1))) :=
    (tail_measurable μ _).mul (by fun_prop)
  calc
    _ = ∫⁻ x, ⨆ n : ℕ, truncate f n x ^ p ∂μ := by simp only [hpow]
    _ = ⨆ n : ℕ, ∫⁻ x, truncate f n x ^ p ∂μ :=
      lintegral_iSup (fun n => (truncate_measurable hf n).pow_const p)
        (fun i j hij x => ENNReal.rpow_le_rpow (truncate_mono f hij x) hp.le)
    _ = ⨆ n : ℕ, ENNReal.ofReal p *
        ∫⁻ t in Ioi (0:ℝ), μ {x | ENNReal.ofReal t < truncate f n x} * ENNReal.ofReal (t^(p-1)) := by
      congr 1
      funext n
      exact finite_layercake μ (truncate_measurable hf n) (truncate_finite f n) hp
    _ = ENNReal.ofReal p *
        ∫⁻ t in Ioi (0:ℝ), ⨆ n : ℕ,
          μ {x | ENNReal.ofReal t < truncate f n x} * ENNReal.ofReal (t^(p-1)) := by
      rw [lintegral_iSup hmeas hmono,ENNReal.mul_iSup]
    _ = _ := by
      congr 1
      apply lintegral_congr
      intro t
      rw [← ENNReal.iSup_mul,← htail]

end
end KakeyaFormal.ENNRealLayerCake
