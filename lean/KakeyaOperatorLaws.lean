import KakeyaOperator

/-! Algebraic and order laws for the actual original-position operator.
Measurability of the output is intentionally proved in a separate geometric
module. Indicator identities below identify the finite real and ENNReal models. -/
namespace KakeyaFormal.KakeyaOperatorLaws
open MeasureTheory Set KakeyaOperator
open scoped ENNReal
noncomputable section

theorem average_mono {n : ℕ} (δ : ℝ) {f g : Space n → ℝ≥0∞}
    (hfg : f ≤ g) (b : Space n) (v : Direction n) : KakeyaOperator.average δ f b v ≤ KakeyaOperator.average δ g b v :=
  ENNReal.div_le_div_right (lintegral_mono hfg) _

theorem maximal_mono {n : ℕ} (δ : ℝ) {f g : Space n → ℝ≥0∞}
    (hfg : f ≤ g) (v : Direction n) : maximal δ f v ≤ maximal δ g v :=
  iSup_mono (fun b => average_mono δ hfg b v)

/-- Null-set changes in the input affect no tube average, at any position. -/
theorem average_ae_mono {n : ℕ} (δ : ℝ) {f g : Space n → ℝ≥0∞}
    (hfg : f ≤ᵐ[(volume : Measure (Space n))] g) (b : Space n) (v : Direction n) :
    KakeyaOperator.average δ f b v ≤ KakeyaOperator.average δ g b v :=
  ENNReal.div_le_div_right (lintegral_mono_ae (ae_restrict_of_ae hfg)) _

theorem maximal_ae_mono {n : ℕ} (δ : ℝ) {f g : Space n → ℝ≥0∞}
    (hfg : f ≤ᵐ[(volume : Measure (Space n))] g) (v : Direction n) :
    maximal δ f v ≤ maximal δ g v :=
  iSup_mono (fun b => average_ae_mono δ hfg b v)

theorem maximal_ae_congr {n : ℕ} (δ : ℝ) {f g : Space n → ℝ≥0∞}
    (hfg : f =ᵐ[(volume : Measure (Space n))] g) (v : Direction n) :
    maximal δ f v = maximal δ g v :=
  le_antisymm (maximal_ae_mono δ hfg.le v) (maximal_ae_mono δ hfg.symm.le v)

theorem average_zero {n : ℕ} (δ : ℝ) (b : Space n) (v : Direction n) :
    KakeyaOperator.average δ (fun _ => 0) b v = 0 := by simp [KakeyaOperator.average]

theorem maximal_zero {n : ℕ} (δ : ℝ) (v : Direction n) :
    maximal δ (fun _ => 0) v = 0 := by simp [maximal,average_zero]

theorem average_const {n : ℕ} {δ : ℝ} (hδ : 0 < δ) (c : ℝ≥0∞)
    (b : Space n) (v : Direction n) : KakeyaOperator.average δ (fun _ => c) b v = c := by
  simp only [KakeyaOperator.average,setLIntegral_const]
  exact ENNReal.mul_div_cancel_right (ne_of_gt (carrier_pos v b hδ)) (carrier_finite v b δ)

theorem maximal_const {n : ℕ} {δ : ℝ} (hδ : 0 < δ) (c : ℝ≥0∞)
    (v : Direction n) : maximal δ (fun _ => c) v = c := by
  simp only [maximal,average_const hδ,ciSup_const]

theorem maximal_le_const {n : ℕ} {δ : ℝ} (hδ : 0 < δ)
    {f : Space n → ℝ≥0∞} {c : ℝ≥0∞} (hfc : ∀ x, f x ≤ c) (v : Direction n) :
    maximal δ f v ≤ c := by
  simpa only [maximal_const hδ] using maximal_mono δ hfc v

/-- Essential infinity bounds imply pointwise bounds on every output direction. -/
theorem maximal_le_const_ae {n : ℕ} {δ : ℝ} (hδ : 0 < δ)
    {f : Space n → ℝ≥0∞} {c : ℝ≥0∞}
    (hfc : ∀ᵐ x ∂(volume : Measure (Space n)), f x ≤ c) (v : Direction n) :
    maximal δ f v ≤ c := by
  simpa only [maximal_const hδ] using maximal_ae_mono δ hfc v

theorem average_add {n : ℕ} (δ : ℝ) {f : Space n → ℝ≥0∞} (hf : Measurable f)
    (g : Space n → ℝ≥0∞) (b : Space n) (v : Direction n) :
    KakeyaOperator.average δ (fun x => f x + g x) b v = KakeyaOperator.average δ f b v + KakeyaOperator.average δ g b v := by
  simp only [KakeyaOperator.average,lintegral_add_left hf,div_eq_mul_inv,add_mul]

theorem maximal_add_le {n : ℕ} (δ : ℝ) {f : Space n → ℝ≥0∞} (hf : Measurable f)
    (g : Space n → ℝ≥0∞) (v : Direction n) :
    maximal δ (fun x => f x + g x) v ≤ maximal δ f v + maximal δ g v := by
  apply iSup_le
  intro b
  rw [average_add δ hf]
  exact add_le_add (le_iSup (fun b : Space n => KakeyaOperator.average δ f b v) b)
    (le_iSup (fun b : Space n => KakeyaOperator.average δ g b v) b)

theorem average_sum {n : ℕ} {ι : Type*} (δ : ℝ) (s : Finset ι)
    (f : ι → Space n → ℝ≥0∞) (hf : ∀ i ∈ s, Measurable (f i))
    (b : Space n) (v : Direction n) :
    KakeyaOperator.average δ (fun x => ∑ i ∈ s, f i x) b v =
      ∑ i ∈ s, KakeyaOperator.average δ (f i) b v := by
  simp only [KakeyaOperator.average,lintegral_finsetSum s hf,div_eq_mul_inv,Finset.sum_mul]

theorem maximal_sum_le {n : ℕ} {ι : Type*} (δ : ℝ) (s : Finset ι)
    (f : ι → Space n → ℝ≥0∞) (hf : ∀ i ∈ s, Measurable (f i)) (v : Direction n) :
    maximal δ (fun x => ∑ i ∈ s, f i x) v ≤ ∑ i ∈ s, maximal δ (f i) v := by
  apply iSup_le
  intro b
  rw [average_sum δ s f hf]
  exact Finset.sum_le_sum (fun i _ => le_iSup (fun b : Space n =>
    KakeyaOperator.average δ (f i) b v) b)

theorem average_const_mul {n : ℕ} (δ : ℝ) (c : ℝ≥0∞)
    {f : Space n → ℝ≥0∞} (hf : Measurable f) (b : Space n) (v : Direction n) :
    KakeyaOperator.average δ (fun x => c*f x) b v = c*KakeyaOperator.average δ f b v := by
  simp only [KakeyaOperator.average,lintegral_const_mul c hf,mul_div_assoc]

theorem maximal_const_mul {n : ℕ} (δ : ℝ) (c : ℝ≥0∞)
    {f : Space n → ℝ≥0∞} (hf : Measurable f) (v : Direction n) :
    maximal δ (fun x => c*f x) v = c*maximal δ f v := by
  simp only [maximal,average_const_mul δ c hf,ENNReal.mul_iSup]

/-- Finite multipliers need no measurability premise on the input. -/
theorem average_finite_mul {n : ℕ} (δ : ℝ) (c : ℝ≥0∞) (hc : c ≠ ∞)
    (f : Space n → ℝ≥0∞) (b : Space n) (v : Direction n) :
    KakeyaOperator.average δ (fun x => c*f x) b v = c*KakeyaOperator.average δ f b v := by
  simp only [KakeyaOperator.average,lintegral_const_mul' c f hc,mul_div_assoc]

theorem maximal_finite_mul {n : ℕ} (δ : ℝ) (c : ℝ≥0∞) (hc : c ≠ ∞)
    (f : Space n → ℝ≥0∞) (v : Direction n) :
    maximal δ (fun x => c*f x) v = c*maximal δ f v := by
  simp only [maximal,average_finite_mul δ c hc,ENNReal.mul_iSup]

theorem average_indicator {n : ℕ} {δ : ℝ} (hδ : 0 < δ)
    (E : Set (Space n)) (hE : MeasurableSet E) (b : Space n) (v : Direction n) :
    KakeyaOperator.average δ (E.indicator (fun _ => 1)) b v = ENNReal.ofReal (indicatorDensity δ E b v) := by
  rw [KakeyaOperator.average,setLIntegral_indicator hE,setLIntegral_const,one_mul,
    indicatorDensity,ENNReal.ofReal_div_of_pos (carrier_real_pos v b hδ)]
  simp only [Measure.real,ENNReal.ofReal_toReal (intersection_finite v b δ E),
    ENNReal.ofReal_toReal (carrier_finite v b δ)]

theorem maximal_indicator_le_one {n : ℕ} {δ : ℝ} (hδ : 0 < δ)
    (E : Set (Space n)) (v : Direction n) :
    maximal δ (E.indicator (fun _ => 1)) v ≤ 1 := by
  apply maximal_le_const hδ _ v
  intro x
  classical
  by_cases hx : x ∈ E <;> simp [hx]

/-- The real supremum and the ENNReal operator are the same indicator operator. -/
theorem maximal_indicator {n : ℕ} {δ : ℝ} (hδ : 0 < δ)
    (E : Set (Space n)) (hE : MeasurableSet E) (v : Direction n) :
    maximal δ (E.indicator (fun _ => 1)) v = ENNReal.ofReal (indicatorMaximal δ E v) := by
  apply le_antisymm
  · apply iSup_le
    intro b
    rw [average_indicator hδ E hE]
    exact ENNReal.ofReal_le_ofReal (indicatorDensity_le_maximal hδ E b v)
  · have hfin : maximal δ (E.indicator (fun _ => 1)) v ≠ ∞ :=
      ne_of_lt ((maximal_indicator_le_one hδ E v).trans_lt (by simp))
    apply (ENNReal.ofReal_le_iff_le_toReal hfin).mpr
    apply ciSup_le
    intro b
    apply (ENNReal.ofReal_le_iff_le_toReal hfin).mp
    rw [← average_indicator hδ E hE]
    exact le_iSup (fun b : Space n => KakeyaOperator.average δ (E.indicator (fun _ => 1)) b v) b

/-- Strict nonnegative levels of the ENNReal operator are literally the real
indicator level sets used in the finite witness construction. -/
theorem indicator_level_eq {n : ℕ} {δ lam : ℝ} (hδ : 0 < δ) (hlam : 0 ≤ lam)
    (E : Set (Space n)) (hE : MeasurableSet E) :
    {v : Direction n | ENNReal.ofReal lam < maximal δ (E.indicator (fun _ => 1)) v} =
      indicatorLevel δ E lam := by
  ext v
  simp only [Set.mem_ofPred_eq,maximal_indicator hδ E hE,indicatorLevel,
    ENNReal.ofReal_lt_ofReal_iff_of_nonneg hlam]

/-- Monotone convergence holds for each actual tube average. -/
theorem average_iSup {n : ℕ} (δ : ℝ) (f : ℕ → Space n → ℝ≥0∞)
    (hf : ∀ j, Measurable (f j)) (hmono : Monotone f) (b : Space n) (v : Direction n) :
    KakeyaOperator.average δ (fun x => ⨆ j, f j x) b v = ⨆ j, KakeyaOperator.average δ (f j) b v := by
  simp only [KakeyaOperator.average,lintegral_iSup hf hmono,div_eq_mul_inv,ENNReal.iSup_mul]

/-- Taking the supremum over all positions commutes with increasing measurable
limits. This gives an exact Fatou compatibility law for monotone extension. -/
theorem maximal_iSup {n : ℕ} (δ : ℝ) (f : ℕ → Space n → ℝ≥0∞)
    (hf : ∀ j, Measurable (f j)) (hmono : Monotone f) (v : Direction n) :
    maximal δ (fun x => ⨆ j, f j x) v = ⨆ j, maximal δ (f j) v := by
  simp only [maximal,average_iSup δ f hf hmono]
  exact iSup_comm

end
end KakeyaFormal.KakeyaOperatorLaws
