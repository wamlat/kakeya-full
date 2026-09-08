import CommonDensityLocalization

/-! Completed-measure common-radius and common-density localization. The selected
sets are literally the ORIGINAL restrictions Y i ∩ closedBall, including when
Y i is not Borel measurable. All choices are constructed from measurable subset
representatives and all physical measures are transferred exactly. -/
namespace KakeyaFormal.LebesgueLocalization
open MeasureTheory Set Finset
open KakeyaFormal.Localization
open scoped BigOperators ENNReal
noncomputable section

variable {I X : Type*} [Fintype I] [MetricSpace X] [MeasurableSpace X] [BorelSpace X]

structure NullSelection (μ : Measure X) (Y : I → Set X) (δ alpha base upper : ℝ) where
  radiusDepth : ℕ
  radiusIndex : Fin (radiusDepth+1)
  densityDepth : ℕ
  densityIndex : Fin (densityDepth+1)
  centers : I → X
  selected : Finset I
  selected_nonempty : selected.Nonempty
  radius_depth_bound : (radiusDepth:ℝ) ≤ Real.log (1/δ)/Real.log 2
  density_depth_bound : (densityDepth:ℝ)+1 ≤
    Real.log (upper / ((radius radiusDepth radiusIndex.val)^alpha*base))/Real.log 2+2
  radius_lower : δ ≤ radius radiusDepth radiusIndex.val
  radius_upper : radius radiusDepth radiusIndex.val ≤ 1
  count_lower : (Fintype.card I:ℝ)/((radiusDepth+1:ℕ)*(densityDepth+1:ℕ)) ≤ selected.card
  localized_nullMeasurable : ∀ i ∈ selected,
    NullMeasurableSet (Y i ∩ Metric.closedBall (centers i) (radius radiusDepth radiusIndex.val)) μ
  original_mass_fraction : ∀ i ∈ selected,
    (radius radiusDepth radiusIndex.val)^alpha*μ.real (Y i) ≤
      μ.real (Y i ∩ Metric.closedBall (centers i) (radius radiusDepth radiusIndex.val))
  density_range : ∀ i ∈ selected,
    ((radius radiusDepth radiusIndex.val)^alpha*base)*(2:ℝ)^densityIndex.val ≤
      μ.real (Y i ∩ Metric.closedBall (centers i) (radius radiusDepth radiusIndex.val)) ∧
    μ.real (Y i ∩ Metric.closedBall (centers i) (radius radiusDepth radiusIndex.val)) <
      2*(((radius radiusDepth radiusIndex.val)^alpha*base)*(2:ℝ)^densityIndex.val)
  two_ends : ∀ i ∈ selected, ∀ y : X, ∀ r : ℝ, δ ≤ r → r ≤ radius radiusDepth radiusIndex.val →
    μ.real ((Y i ∩ Metric.closedBall (centers i) (radius radiusDepth radiusIndex.val)) ∩ Metric.closedBall y r) ≤
      (4:ℝ)^alpha*(r/(radius radiusDepth radiusIndex.val))^alpha*
        μ.real (Y i ∩ Metric.closedBall (centers i) (radius radiusDepth radiusIndex.val))

/-- Literal completed-measurable version of the two common class selections in
Lemma 3.1, with the original restrictions and no supplied selection premise. -/
theorem exists_selection (μ : Measure X) (Y : I → Set X)
    (hY : ∀ i, NullMeasurableSet (Y i) μ) (hfinite : ∀ i, μ (Y i) ≠ ∞)
    {δ alpha base upper : ℝ} (hδ : 0 < δ) (hδ1 : δ ≤ 1) (ha : 0 ≤ alpha)
    (hbase : 0 < base) (hI : 0 < Fintype.card I)
    (hlower : ∀ i, base ≤ μ.real (Y i)) (hupper : ∀ i, μ.real (Y i) ≤ upper)
    (x₀ : I → X) (hcover : ∀ i, Y i ⊆ Metric.closedBall (x₀ i) 1) :
    Nonempty (NullSelection μ Y δ alpha base upper) := by
  classical
  choose Z hsub hZm hZae using fun i => (hY i).exists_measurable_subset_ae_eq
  have hmass (i : I) : μ.real (Z i) = μ.real (Y i) := measureReal_congr (hZae i)
  have hinter (i : I) (E : Set X) : μ.real (Z i ∩ E) = μ.real (Y i ∩ E) :=
    measureReal_congr ((hZae i).inter Filter.EventuallyEq.rfl)
  obtain ⟨S⟩ := CommonDensityLocalization.exists_selection μ Z hZm
    (fun i => (measure_congr (hZae i)).trans_ne (hfinite i)) hδ hδ1 ha hbase hI
    (fun i => by rw [hmass]; exact hlower i)
    (fun i => by rw [hmass]; exact hupper i) x₀ (fun i => (hsub i).trans (hcover i))
  refine ⟨{
    radiusDepth := S.radiusDepth
    radiusIndex := S.radiusIndex
    densityDepth := S.densityDepth
    densityIndex := S.densityIndex
    centers := S.centers
    selected := S.selected
    selected_nonempty := S.selected_nonempty
    radius_depth_bound := S.radius_depth_bound
    density_depth_bound := S.density_depth_bound
    radius_lower := S.radius_lower
    radius_upper := S.radius_upper
    count_lower := S.count_lower
    localized_nullMeasurable := fun i _ => (hY i).inter measurableSet_closedBall.nullMeasurableSet
    original_mass_fraction := ?_
    density_range := ?_
    two_ends := ?_ }⟩
  · intro i hi
    simpa only [hmass, hinter] using S.original_mass_fraction i hi
  · intro i hi
    simpa only [hinter] using S.density_range i hi
  · intro i hi y r hlow hhigh
    have h := S.two_ends i hi y r hlow hhigh
    simpa only [Set.inter_assoc, hinter] using h

omit [BorelSpace X] in
/-- The common localized density is at least the radius-to-alpha fraction of
the original lower density. This follows from the constructed dyadic index. -/
theorem NullSelection.common_mass_lower {μ : Measure X} {Y : I → Set X} {δ alpha base upper : ℝ}
    (s : NullSelection μ Y δ alpha base upper) (hδ : 0 < δ) (hbase : 0 ≤ base) :
    (radius s.radiusDepth s.radiusIndex.val)^alpha*base ≤
      ((radius s.radiusDepth s.radiusIndex.val)^alpha*base)*(2:ℝ)^s.densityIndex.val := by
  have hpow : (1:ℝ) ≤ (2:ℝ)^s.densityIndex.val := one_le_pow₀ (by norm_num)
  simpa only [mul_one] using mul_le_mul_of_nonneg_left hpow
    (mul_nonneg (Real.rpow_nonneg (hδ.le.trans s.radius_lower) alpha) hbase)

omit [BorelSpace X] in
/-- The second class budget is logarithmic in the original mass ratio and the
mesh scale; no hidden dependence on the selected radius remains. -/
theorem NullSelection.density_depth_log_bound {μ : Measure X} {Y : I → Set X}
    {δ alpha base upper : ℝ} (s : NullSelection μ Y δ alpha base upper)
    (hδ : 0 < δ) (ha : 0 ≤ alpha) (hbase : 0 < base) (hupper : 0 < upper) :
    (s.densityDepth:ℝ)+1 ≤ Real.log (upper/base)/Real.log 2 +
      alpha*(Real.log (1/δ)/Real.log 2)+2 := by
  have hrho : 0 < radius s.radiusDepth s.radiusIndex.val := hδ.trans_le s.radius_lower
  have hlog := Real.log_le_log hδ s.radius_lower
  have hmult := mul_le_mul_of_nonneg_left hlog ha
  have hcompare : Real.log (upper/((radius s.radiusDepth s.radiusIndex.val)^alpha*base)) ≤
      Real.log (upper/base)+alpha*Real.log (1/δ) := by
    rw [Real.log_div hupper.ne' (mul_pos (Real.rpow_pos_of_pos hrho alpha) hbase).ne',
      Real.log_mul (Real.rpow_pos_of_pos hrho alpha).ne' hbase.ne',Real.log_rpow hrho,
      Real.log_div hupper.ne' hbase.ne',one_div,Real.log_inv]
    nlinarith
  have hh := div_le_div_of_nonneg_right hcompare (Real.log_pos (by norm_num : (1:ℝ)<2)).le
  rw [add_div,mul_div_assoc] at hh
  exact s.density_depth_bound.trans (by linarith)

end
end KakeyaFormal.LebesgueLocalization
